package com.example.calculadoracientifica

import android.annotation.SuppressLint
import android.content.res.ColorStateList
import android.graphics.Color
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.os.Build
import android.os.Bundle
import android.provider.Settings
import android.text.Editable
import android.text.TextWatcher
import android.view.MotionEvent
import android.view.View
import android.view.WindowManager
import android.view.animation.DecelerateInterpolator
import android.view.animation.OvershootInterpolator
import android.widget.Button
import android.widget.EditText
import android.widget.TextView
import androidx.appcompat.app.AppCompatActivity
import androidx.core.graphics.ColorUtils
import androidx.core.view.ViewCompat
import androidx.core.view.WindowCompat
import androidx.core.view.WindowInsetsCompat
import java.math.BigDecimal
import java.math.MathContext
import kotlin.math.abs
import kotlin.math.cos
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt
import kotlin.math.sin
import kotlin.math.tan

// =====================================================================
//  MOTOR MATEMÁTICO (parser de precedencia, sin eval)
// =====================================================================

class CalcException(message: String) : Exception(message)

object ExpressionEvaluator {

    private sealed class Tok {
        class Num(val v: Double) : Tok()
        class Op(val c: Char) : Tok()      // '+', '-', '*', '/'
        class Fn(val name: String) : Tok()
        object LP : Tok()
        object RP : Tok()
    }

    private fun isDigit(c: Char) = c in '0'..'9'

    private fun tokenize(s: String): List<Tok> {
        val out = ArrayList<Tok>()
        var i = 0
        while (i < s.length) {
            val ch = s[i]
            when {
                ch.isWhitespace() -> i++
                isDigit(ch) || ch == '.' -> {
                    val st = i
                    var dots = 0
                    while (i < s.length && (isDigit(s[i]) || s[i] == '.')) {
                        if (s[i] == '.') dots++
                        i++
                    }
                    if (dots > 1) throw CalcException("Número no válido")
                    if (s.substring(st, i) == ".") throw CalcException("Número no válido")
                    // Notación científica (por ejemplo 1.5E+12), generada por resultados grandes
                    if (i < s.length && s[i] == 'E') {
                        var j = i + 1
                        if (j < s.length && (s[j] == '+' || s[j] == '-' || s[j] == '−')) j++
                        if (j < s.length && isDigit(s[j])) {
                            while (j < s.length && isDigit(s[j])) j++
                            i = j
                        }
                    }
                    val text = s.substring(st, i).replace('−', '-')
                    val v = text.toDoubleOrNull() ?: throw CalcException("Número no válido")
                    out.add(Tok.Num(v))
                }
                ch == '+' -> { out.add(Tok.Op('+')); i++ }
                ch == '-' || ch == '−' -> { out.add(Tok.Op('-')); i++ }
                ch == '×' || ch == '*' -> { out.add(Tok.Op('*')); i++ }
                ch == '÷' || ch == '/' -> { out.add(Tok.Op('/')); i++ }
                ch == '^' -> { out.add(Tok.Op('^')); i++ }
                ch == '(' -> { out.add(Tok.LP); i++ }
                ch == ')' -> { out.add(Tok.RP); i++ }
                ch.isLetter() -> {
                    val st = i
                    while (i < s.length && s[i].isLetter()) i++
                    val name = s.substring(st, i).lowercase()
                    if (name != "sin" && name != "cos" && name != "tan") {
                        throw CalcException("Función desconocida: $name")
                    }
                    out.add(Tok.Fn(name))
                }
                else -> throw CalcException("Carácter no válido: $ch")
            }
        }
        return out
    }

    private class Parser(private val t: List<Tok>, private val deg: Boolean) {
        private var p = 0

        private fun peek(): Tok? = if (p < t.size) t[p] else null

        fun parse(): Double {
            if (t.isEmpty()) throw CalcException("Expresión vacía")
            val v = expr()
            if (p < t.size) {
                if (peek() is Tok.RP) throw CalcException("Paréntesis de cierre sin apertura")
                throw CalcException("Error de sintaxis")
            }
            return v
        }

        // expr := term (('+' | '-') term)*
        private fun expr(): Double {
            var v = term()
            while (true) {
                val k = peek()
                if (k is Tok.Op && (k.c == '+' || k.c == '-')) {
                    p++
                    val r = term()
                    v = if (k.c == '+') v + r else v - r
                } else break
            }
            return v
        }

        // term := unary (('*' | '/') unary | implicit unary)*
        private fun term(): Double {
            var v = unary()
            while (true) {
                val k = peek()
                if (k is Tok.Op && (k.c == '*' || k.c == '/')) {
                    p++
                    val r = unary()
                    if (k.c == '*') {
                        v *= r
                    } else {
                        if (r == 0.0) throw CalcException("No se puede dividir entre 0")
                        v /= r
                    }
                } else if (k is Tok.Num || k is Tok.Fn || k is Tok.LP) {
                    v *= unary() // multiplicación implícita: 2(3), 2sin(30)
                } else break
            }
            return v
        }

        // unary := ('+' | '-') unary | primary
        private fun unary(): Double {
            val k = peek()
            if (k is Tok.Op && (k.c == '+' || k.c == '-')) {
                p++
                val v = unary()
                return if (k.c == '-') -v else v
            }
            return power()
        }

        // power := primary ('^' unary)?   (asociativa a la derecha: 2^3^2 = 2^9; 2^-1 permitido)
        private fun power(): Double {
            val base = primary()
            val k = peek()
            if (k is Tok.Op && k.c == '^') {
                p++
                val ex = unary()
                return pow(base, ex)
            }
            return base
        }

        private fun pow(b: Double, ex: Double): Double {
            if (b == 0.0 && ex == 0.0) throw CalcException("0^0 no está definido")
            if (b == 0.0 && ex < 0.0) throw CalcException("No se puede dividir entre 0")
            val r = Math.pow(b, ex)
            if (r.isNaN()) throw CalcException("Resultado no real")
            if (r.isInfinite()) throw CalcException("Valor no válido")
            return r
        }

        // primary := NUM | '(' expr ')' | FN '(' expr ')'
        private fun primary(): Double {
            val k = peek() ?: throw CalcException("Expresión incompleta")
            p++
            return when (k) {
                is Tok.Num -> k.v
                is Tok.LP -> {
                    val v = expr()
                    close()
                    v
                }
                is Tok.Fn -> {
                    if (peek() !is Tok.LP) throw CalcException("Falta '(' después de ${k.name}")
                    p++
                    val v = expr()
                    close()
                    apply(k.name, v)
                }
                is Tok.RP -> throw CalcException("Error de sintaxis")
                is Tok.Op -> throw CalcException("Error de sintaxis")
            }
        }

        private fun close() {
            if (peek() !is Tok.RP) throw CalcException("Paréntesis incompletos")
            p++
        }

        private fun apply(name: String, x: Double): Double {
            if (x.isNaN() || x.isInfinite()) throw CalcException("Valor no válido")
            val r: Double
            if (deg) {
                when (name) {
                    "sin" -> r = if (x % 180.0 == 0.0) 0.0 else sin(Math.toRadians(x % 360.0))
                    "cos" -> r = if ((x - 90.0) % 180.0 == 0.0) 0.0 else cos(Math.toRadians(x % 360.0))
                    else -> {
                        if ((x - 90.0) % 180.0 == 0.0) throw CalcException("Tangente indefinida")
                        r = if (x % 180.0 == 0.0) 0.0 else tan(Math.toRadians(x % 360.0))
                    }
                }
            } else {
                when (name) {
                    "sin" -> r = sin(x)
                    "cos" -> r = cos(x)
                    else -> {
                        if (abs(cos(x)) < 1e-12) throw CalcException("Tangente indefinida")
                        r = tan(x)
                    }
                }
            }
            return if (abs(r) < 1e-15) 0.0 else r
        }
    }

    fun evaluate(expression: String, deg: Boolean): Double {
        try {
            val v = Parser(tokenize(expression), deg).parse()
            if (v.isNaN() || v.isInfinite()) throw CalcException("Valor no válido")
            return v
        } catch (e: StackOverflowError) {
            throw CalcException("Expresión demasiado compleja")
        }
    }

    fun format(v: Double): String {
        if (abs(v) < 1e-14) return "0"
        val bd = BigDecimal(v).round(MathContext(12)).stripTrailingZeros()
        val a = abs(v)
        return if (a >= 1e12 || a < 1e-6) bd.toString() else bd.toPlainString()
    }
}

// =====================================================================
//  ACTIVIDAD PRINCIPAL
// =====================================================================

private fun col(s: String): Int = Color.parseColor(s)

class MainActivity : AppCompatActivity() {

    private enum class Kind { NUM, FUNC, OP, EQ, CLR, HDR }

    /** Paleta de colores; se interpola para animar el cambio de tema. */
    private class Palette(val c: IntArray) {
        val bg get() = c[0]
        val card get() = c[1]
        val stroke get() = c[2]
        val text get() = c[3]
        val textSec get() = c[4]
        val numBg get() = c[5]
        val numText get() = c[6]
        val funcBg get() = c[7]
        val funcText get() = c[8]
        val opBg get() = c[9]
        val opText get() = c[10]
        val eqBg get() = c[11]
        val eqText get() = c[12]
        val clrBg get() = c[13]
        val clrText get() = c[14]
        val blob1 get() = c[15]
        val blob2 get() = c[16]
        val panel get() = c[17]
        val item get() = c[18]
        val hdrBg get() = c[19]
        val hdrText get() = c[20]

        companion object {
            val PINK_LIGHT = Palette(intArrayOf(
                col("#FFF5F8"), col("#FFFFFF"), col("#FF2E93"), col("#2B1220"), col("#8A5A73"),
                col("#FFE3EE"), col("#3A1A2A"), col("#FFC9DE"), col("#7A1050"), col("#FF6FAE"),
                col("#3A0A24"), col("#E0147F"), col("#FFFFFF"), col("#FFB3CF"), col("#B0004F"),
                col("#40FF2E93"), col("#40C026D3"), col("#FFF0F6"), col("#FFFFFF"), col("#FFE3EE"),
                col("#7A1050")
            ))
        }
    }

    // ---- Vistas ----
    private lateinit var root: View
    private lateinit var blobTop: View
    private lateinit var blobBottom: View
    private lateinit var displayCard: View
    private lateinit var tvTitle: TextView
    private lateinit var tvAngle: TextView
    private lateinit var tvResult: TextView
    private lateinit var etExpression: EditText
    private lateinit var btnAngle: Button

    // ---- Drawables ----
    private val blob1Bg = GradientDrawable().apply { shape = GradientDrawable.OVAL }
    private val blob2Bg = GradientDrawable().apply { shape = GradientDrawable.OVAL }
    private val cardBg = GradientDrawable()
    private val cursorDrawable = GradientDrawable()
    private val titleBg = GradientDrawable()

    // ---- Estado ----
    private var cur: Palette = Palette.PINK_LIGHT
    private var deg = true
    private var justEvaluated = false
    private var lastResult: String? = null
    private var resultState = 0 // 0 = vista previa, 1 = final, 2 = error
    private val keys = ArrayList<Key>()

    private val numberOnly = Regex("^[-−+]?[0-9.]*$")

    companion object {
        private const val MAX_LENGTH = 300
    }

    // =================================================================
    //  Ciclo de vida
    // =================================================================

    @SuppressLint("ClickableViewAccessibility")
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        WindowCompat.setDecorFitsSystemWindows(window, false)
        window.setSoftInputMode(WindowManager.LayoutParams.SOFT_INPUT_STATE_ALWAYS_HIDDEN)
        setContentView(R.layout.activity_main)

        bindViews()

        setupDrawables()
        setupKeys()

        // Pantalla de expresión: el cursor se puede mover y no aparece el teclado del sistema
        etExpression.showSoftInputOnFocus = false
        etExpression.setOnTouchListener { _, _ ->
            justEvaluated = false
            false
        }
        etExpression.requestFocus()

        applyPalette(cur)
        updateSystemBars()
        refreshAngleUi()

        etExpression.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) {}
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) {}
            override fun afterTextChanged(s: Editable?) {
                updatePreview()
            }
        })
        updatePreview()

        ViewCompat.setOnApplyWindowInsetsListener(root) { v, insets ->
            val bars = insets.getInsets(
                WindowInsetsCompat.Type.systemBars() or WindowInsetsCompat.Type.displayCutout()
            )
            v.setPadding(bars.left, bars.top, bars.right, bars.bottom)
            WindowInsetsCompat.CONSUMED
        }
        ViewCompat.requestApplyInsets(root)
    }

    // =================================================================
    //  Inicialización de vistas
    // =================================================================

    private fun bindViews() {
        root = findViewById(R.id.root)
        blobTop = findViewById(R.id.blobTop)
        blobBottom = findViewById(R.id.blobBottom)
        displayCard = findViewById(R.id.displayCard)
        tvTitle = findViewById(R.id.tvTitle)
        tvAngle = findViewById(R.id.tvAngleMode)
        tvResult = findViewById(R.id.tvResult)
        etExpression = findViewById(R.id.etExpression)
        btnAngle = findViewById(R.id.btnAngle)
    }

    private fun setupDrawables() {
        blobTop.background = blob1Bg
        blobBottom.background = blob2Bg
        cardBg.cornerRadius = dpF(22)
        displayCard.background = cardBg
        titleBg.cornerRadius = dpF(14)
        tvTitle.background = titleBg
        if (Build.VERSION.SDK_INT >= 29) {
            cursorDrawable.setSize(dp(2), -1)
            etExpression.textCursorDrawable = cursorDrawable
        }
    }

    private fun setupKeys() {
        // Dígitos
        val digitIds = intArrayOf(
            R.id.btn0, R.id.btn1, R.id.btn2, R.id.btn3, R.id.btn4,
            R.id.btn5, R.id.btn6, R.id.btn7, R.id.btn8, R.id.btn9
        )
        for (d in 0..9) {
            key(digitIds[d], Kind.NUM) { inputDigit(d.toString()) }
        }
        key(R.id.btnDot, Kind.NUM) { inputDot() }

        // Operadores
        key(R.id.btnAdd, Kind.OP) { inputOperator('+') }
        key(R.id.btnSubtract, Kind.OP) { inputOperator('−') }
        key(R.id.btnMultiply, Kind.OP) { inputOperator('×') }
        key(R.id.btnDivide, Kind.OP) { inputOperator('÷') }

        // Funciones científicas y paréntesis
        key(R.id.btnSin, Kind.FUNC) { inputFunction("sin") }
        key(R.id.btnCos, Kind.FUNC) { inputFunction("cos") }
        key(R.id.btnTan, Kind.FUNC) { inputFunction("tan") }
        key(R.id.btnOpen, Kind.FUNC) { inputOpen() }
        key(R.id.btnClose, Kind.FUNC) { inputClose() }
        key(R.id.btnPow, Kind.FUNC) { inputOperator('^') }

        // Control
        key(R.id.btnClear, Kind.CLR) { clearAll() }
        val back = key(R.id.btnBackspace, Kind.CLR) { backspace() }
        back.setOnLongClickListener {
            clearAll()
            true
        }
        key(R.id.btnEquals, Kind.EQ) { calculate() }

        // Encabezado
        key(R.id.btnAngle, Kind.HDR) { toggleAngle() }
    }

    // =================================================================
    //  Botones: estilo, sonido y animación de pulsación
    // =================================================================

    private inner class Key(val view: Button, val kind: Kind) {
        private val radius = dpF(if (kind == Kind.HDR) 14 else 18)
        private val fill = GradientDrawable().apply { cornerRadius = radius }
        private val ripple: RippleDrawable

        init {
            val mask = GradientDrawable().apply {
                cornerRadius = radius
                setColor(Color.WHITE)
            }
            ripple = RippleDrawable(ColorStateList.valueOf(col("#55FF2E93")), fill, mask)
            view.background = ripple
        }

        fun refresh(p: Palette) {
            val bgColor = when (kind) {
                Kind.NUM -> p.numBg
                Kind.FUNC -> p.funcBg
                Kind.OP -> p.opBg
                Kind.EQ -> p.eqBg
                Kind.CLR -> p.clrBg
                Kind.HDR -> p.hdrBg
            }
            val txtColor = when (kind) {
                Kind.NUM -> p.numText
                Kind.FUNC -> p.funcText
                Kind.OP -> p.opText
                Kind.EQ -> p.eqText
                Kind.CLR -> p.clrText
                Kind.HDR -> p.hdrText
            }
            val strokeAlpha = when (kind) {
                Kind.EQ -> 255
                Kind.OP -> 200
                Kind.FUNC, Kind.CLR -> 140
                Kind.HDR -> 120
                Kind.NUM -> 70
            }
            fill.setColor(bgColor)
            fill.setStroke(
                if (kind == Kind.EQ) dp(2) else dp(1),
                ColorUtils.setAlphaComponent(p.stroke, strokeAlpha)
            )
            view.setTextColor(txtColor)
            ripple.setColor(ColorStateList.valueOf(ColorUtils.setAlphaComponent(p.stroke, 0x55)))
        }
    }

    @SuppressLint("ClickableViewAccessibility")
    private fun key(id: Int, kind: Kind, action: () -> Unit): Button {
        val b = findViewById<Button>(id)
        keys.add(Key(b, kind))
        b.setOnClickListener {
            action()
        }
        b.setOnTouchListener { v, ev ->
            when (ev.actionMasked) {
                MotionEvent.ACTION_DOWN -> if (animationsEnabled()) {
                    v.animate().scaleX(0.92f).scaleY(0.92f).setDuration(70).start()
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    v.animate().scaleX(1f).scaleY(1f).setDuration(160)
                        .setInterpolator(OvershootInterpolator()).start()
                }
            }
            false
        }
        return b
    }

    // =================================================================
    //  Edición de la expresión
    // =================================================================

    private fun selRange(): Pair<Int, Int> {
        val len = etExpression.text.length
        var a = etExpression.selectionStart
        var b = etExpression.selectionEnd
        if (a < 0 || b < 0) {
            a = len
            b = len
        }
        return Pair(min(a, b), max(a, b))
    }

    private fun insertText(t: String) {
        val (a, b) = selRange()
        val e = etExpression.text
        if (e.length - (b - a) + t.length > MAX_LENGTH) return
        e.replace(a, b, t)
        etExpression.setSelection(a + t.length)
    }

    private fun startFreshIfNeeded() {
        if (justEvaluated) {
            justEvaluated = false
            etExpression.setText("")
        }
    }

    private fun isDigitChar(c: Char?) = c != null && c in '0'..'9'

    private fun isOpChar(c: Char?) = c == '+' || c == '−' || c == '×' || c == '÷' || c == '^'

    private fun inputDigit(d: String) {
        startFreshIfNeeded()
        insertText(d)
    }

    private fun inputDot() {
        startFreshIfNeeded()
        val (a, b) = selRange()
        val s = etExpression.text.toString()
        var l = a
        while (l > 0 && (isDigitChar(s[l - 1]) || s[l - 1] == '.')) l--
        var r = b
        while (r < s.length && (isDigitChar(s[r]) || s[r] == '.')) r++
        if ((s.substring(l, a) + s.substring(b, r)).contains('.')) return
        val prev = if (a > 0) s[a - 1] else null
        val ins = when {
            prev == null -> "0."
            isDigitChar(prev) -> "."
            prev == ')' -> "×0."
            else -> "0."
        }
        insertText(ins)
    }

    private fun inputOperator(c: Char) {
        if (justEvaluated) {
            val r = lastResult
            justEvaluated = false
            if (r != null) {
                val e = r.replace('-', '−')
                etExpression.setText(e)
                etExpression.setSelection(e.length)
            }
        }
        val (a, b) = selRange()
        val s = etExpression.text.toString()
        val prev = if (a > 0) s[a - 1] else null
        when {
            a != b -> insertText(c.toString())
            prev == null || prev == '(' -> {
                if (c == '−') insertText("−") // solo se permite el signo negativo
            }
            isOpChar(prev) -> {
                val prev2 = if (a > 1) s[a - 2] else null
                val e = etExpression.text
                if (c == '−' && (prev == '×' || prev == '÷' || prev == '^')) {
                    insertText("−") // 2×−3
                } else if (prev == '−' && (prev2 == '×' || prev2 == '÷' || prev2 == '^') && c != '−') {
                    e.replace(a - 2, a, c.toString()) // 2×−  →  2+
                    etExpression.setSelection(a - 1)
                } else {
                    if ((c == '×' || c == '÷' || c == '^') && (prev2 == null || prev2 == '(')) return
                    e.replace(a - 1, a, c.toString())
                    etExpression.setSelection(a)
                }
            }
            else -> insertText(c.toString())
        }
    }

    private fun inputFunction(name: String) {
        startFreshIfNeeded()
        insertText("$name(")
    }

    private fun inputOpen() {
        startFreshIfNeeded()
        insertText("(")
    }

    private fun inputClose() {
        val (a, _) = selRange()
        val s = etExpression.text.toString()
        val before = s.substring(0, a)
        val open = before.count { it == '(' } - before.count { it == ')' }
        val prev = if (a > 0) s[a - 1] else null
        if (open > 0 && (isDigitChar(prev) || prev == '.' || prev == ')')) insertText(")")
    }

    private fun backspace() {
        justEvaluated = false
        val (a, b) = selRange()
        val e = etExpression.text
        if (a != b) {
            e.delete(a, b)
            etExpression.setSelection(a)
        } else if (a > 0) {
            val before = e.substring(0, a)
            val n = if (before.endsWith("sin(") || before.endsWith("cos(") || before.endsWith("tan(")) 4 else 1
            e.delete(a - n, a)
            etExpression.setSelection(a - n)
        }
    }

    private fun clearAll() {
        justEvaluated = false
        lastResult = null
        etExpression.setText("")
        showResult("", 0)
    }

    // =================================================================
    //  Cálculo y resultados
    // =================================================================

    private fun updatePreview() {
        val s = etExpression.text.toString().trim()
        if (s.isEmpty() || numberOnly.matches(s)) {
            showResult("", 0)
            return
        }
        try {
            showResult(ExpressionEvaluator.format(ExpressionEvaluator.evaluate(s, deg)), 0)
        } catch (e: CalcException) {
            showResult("", 0)
        } catch (e: Exception) {
            showResult("", 0)
        }
    }

    private fun calculate() {
        val s = etExpression.text.toString().trim()
        if (s.isEmpty()) return
        try {
            val r = ExpressionEvaluator.format(ExpressionEvaluator.evaluate(s, deg))
            lastResult = r
            justEvaluated = true
            showResult(r, 1)
            animateResult()
        } catch (e: CalcException) {
            lastResult = null
            justEvaluated = false
            showResult(e.message ?: "Error", 2)
            animateResult()
        } catch (e: Exception) {
            lastResult = null
            justEvaluated = false
            showResult("Error", 2)
        }
    }

    private fun resultColor(): Int = when (resultState) {
        0 -> cur.textSec
        1 -> cur.text
        else -> col("#C62828")
    }

    private fun showResult(text: String, state: Int) {
        resultState = state
        tvResult.text = text
        tvResult.setTextColor(resultColor())
    }

    private fun animateResult() {
        if (!animationsEnabled()) return
        tvResult.alpha = 0f
        tvResult.translationY = dpF(12)
        tvResult.animate().alpha(1f).translationY(0f).setDuration(220)
            .setInterpolator(DecelerateInterpolator()).start()
    }

    private fun toggleAngle() {
        deg = !deg
        refreshAngleUi()
        if (justEvaluated) calculate() else updatePreview()
    }

    private fun refreshAngleUi() {
        btnAngle.text = if (deg) "DEG" else "RAD"
        tvAngle.text = if (deg) "DEG · GRADOS" else "RAD · RADIANES"
        btnAngle.contentDescription =
            if (deg) "Modo grados activo. Pulsa para usar radianes" else "Modo radianes activo. Pulsa para usar grados"
    }

    // =================================================================
    //  Temas, colores y animaciones
    // =================================================================

    private fun updateSystemBars() {
        val ctl = WindowCompat.getInsetsController(window, root)
        ctl.isAppearanceLightStatusBars = true
        ctl.isAppearanceLightNavigationBars = true
    }

    private fun applyPalette(p: Palette) {
        cur = p
        root.setBackgroundColor(p.bg)
        window.decorView.setBackgroundColor(p.bg)
        blob1Bg.setColor(p.blob1)
        blob2Bg.setColor(p.blob2)

        cardBg.setColor(p.card)
        cardBg.setStroke(dp(2), p.stroke)
        cursorDrawable.setColor(p.stroke)

        tvTitle.setTextColor(p.text)
        titleBg.setColor(p.hdrBg)
        titleBg.setStroke(dp(1), ColorUtils.setAlphaComponent(p.stroke, 140))
        tvTitle.setShadowLayer(16f, 0f, 0f, ColorUtils.setAlphaComponent(p.stroke, 150))
        tvAngle.setTextColor(p.funcText)
        etExpression.setTextColor(p.text)
        etExpression.setHintTextColor(p.textSec)
        tvResult.setTextColor(resultColor())

        for (k in keys) k.refresh(p)
    }

    private fun animationsEnabled(): Boolean = try {
        Settings.Global.getFloat(contentResolver, Settings.Global.ANIMATOR_DURATION_SCALE, 1f) != 0f
    } catch (e: Exception) {
        true
    }

    // =================================================================
    //  Utilidades
    // =================================================================

    private fun dpF(v: Int): Float = v * resources.displayMetrics.density

    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).roundToInt()
}