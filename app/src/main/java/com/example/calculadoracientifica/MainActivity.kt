package com.example.calculadoracientifica

import android.animation.Animator
import android.animation.AnimatorListenerAdapter
import android.animation.ValueAnimator
import android.annotation.SuppressLint
import android.content.SharedPreferences
import android.content.res.ColorStateList
import android.content.res.Configuration
import android.graphics.Color
import android.graphics.drawable.ColorDrawable
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.RippleDrawable
import android.hardware.Sensor
import android.hardware.SensorEvent
import android.hardware.SensorEventListener
import android.hardware.SensorManager
import android.media.AudioManager
import android.media.ToneGenerator
import android.os.Build
import android.os.Bundle
import android.provider.Settings
import android.text.Editable
import android.text.TextWatcher
import android.view.Gravity
import android.view.MotionEvent
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.view.animation.DecelerateInterpolator
import android.view.animation.OvershootInterpolator
import android.widget.AbsListView
import android.widget.BaseAdapter
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ListView
import android.widget.PopupWindow
import android.widget.TextView
import android.widget.Toast
import androidx.activity.OnBackPressedCallback
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.core.graphics.ColorUtils
import androidx.core.view.ViewCompat
import androidx.core.view.WindowCompat
import androidx.core.view.WindowInsetsCompat
import org.json.JSONArray
import org.json.JSONObject
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

private data class HistoryItem(val expr: String, val result: String)

private class HistoryHolder(
    val row: LinearLayout,
    val bg: GradientDrawable,
    val expr: TextView,
    val res: TextView,
    val del: TextView
) {
    var pos = 0
}

private fun col(s: String): Int = Color.parseColor(s)

class MainActivity : AppCompatActivity() {

    private enum class Kind { NUM, FUNC, OP, EQ, CLR, HDR }

    private enum class Accent { BLUE, PINK, GREEN }

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
            fun lerp(a: Palette, b: Palette, t: Float) =
                Palette(IntArray(a.c.size) { ColorUtils.blendARGB(a.c[it], b.c[it], t) })

            val PINK_LIGHT = Palette(intArrayOf(
                col("#FFF5F8"), col("#FFFFFF"), col("#FF2E93"), col("#2B1220"), col("#8A5A73"),
                col("#FFE3EE"), col("#3A1A2A"), col("#FFC9DE"), col("#7A1050"), col("#FF6FAE"),
                col("#3A0A24"), col("#E0147F"), col("#FFFFFF"), col("#FFB3CF"), col("#B0004F"),
                col("#40FF2E93"), col("#40C026D3"), col("#FFF0F6"), col("#FFFFFF"), col("#FFE3EE"),
                col("#7A1050")
            ))
            val PINK_DARK = Palette(intArrayOf(
                col("#120A10"), col("#1E1119"), col("#FF2E93"), col("#FFF0F6"), col("#C79AB2"),
                col("#3A1B2D"), col("#FFE4F0"), col("#5A1D45"), col("#FFB6DA"), col("#8E1A5C"),
                col("#FFFFFF"), col("#FF2E93"), col("#18060F"), col("#4A1230"), col("#FF7AB6"),
                col("#55FF2E93"), col("#55B01EC8"), col("#1A0E16"), col("#2A1623"), col("#2A1623"),
                col("#FFB6DA")
            ))
            val BLUE_LIGHT = Palette(intArrayOf(
                col("#F3F8FF"), col("#FFFFFF"), col("#2E7BFF"), col("#0F1D33"), col("#4F6A8F"),
                col("#DCEBFF"), col("#12233F"), col("#B9D5FF"), col("#0B3A8C"), col("#5E9BFF"),
                col("#04122B"), col("#1558D6"), col("#FFFFFF"), col("#A9C8FF"), col("#0A3A8F"),
                col("#402E7BFF"), col("#4026C6DA"), col("#EEF5FF"), col("#FFFFFF"), col("#DCEBFF"),
                col("#0B3A8C")
            ))
            val BLUE_DARK = Palette(intArrayOf(
                col("#08101C"), col("#101B2E"), col("#3D8BFF"), col("#EAF3FF"), col("#93AFD6"),
                col("#1B2D4A"), col("#E1EEFF"), col("#23407A"), col("#A9CCFF"), col("#1F52B5"),
                col("#FFFFFF"), col("#3D8BFF"), col("#04122B"), col("#1A3566"), col("#8DBBFF"),
                col("#553D8BFF"), col("#5522B8CF"), col("#0D1626"), col("#172640"), col("#172640"),
                col("#A9CCFF")
            ))
            val GREEN_LIGHT = Palette(intArrayOf(
                col("#F2FBF5"), col("#FFFFFF"), col("#14C46B"), col("#0F2A1B"), col("#4C7660"),
                col("#DDF4E6"), col("#123524"), col("#B8E8CB"), col("#0B5A33"), col("#4FD18A"),
                col("#04281A"), col("#0B7F45"), col("#FFFFFF"), col("#A8E3C0"), col("#0A5A30"),
                col("#4014C46B"), col("#4000B8A9"), col("#EDFAF2"), col("#FFFFFF"), col("#DDF4E6"),
                col("#0B5A33")
            ))
            val GREEN_DARK = Palette(intArrayOf(
                col("#08130D"), col("#0F1F16"), col("#22E07A"), col("#EAFBF1"), col("#96C7AB"),
                col("#1A3326"), col("#DFF8EA"), col("#1F5A3A"), col("#A8F0C8"), col("#17804A"),
                col("#FFFFFF"), col("#22E07A"), col("#04170D"), col("#17402B"), col("#7DF0B0"),
                col("#5522E07A"), col("#5500B8A9"), col("#0C1A12"), col("#16291E"), col("#16291E"),
                col("#A8F0C8")
            ))

            fun get(accent: Accent, dark: Boolean): Palette = when (accent) {
                Accent.BLUE -> if (dark) BLUE_DARK else BLUE_LIGHT
                Accent.PINK -> if (dark) PINK_DARK else PINK_LIGHT
                Accent.GREEN -> if (dark) GREEN_DARK else GREEN_LIGHT
            }
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
    private lateinit var btnMenu: Button
    private lateinit var rowSci: View
    private lateinit var historyPanel: View
    private lateinit var tvHistoryTitle: TextView
    private lateinit var tvHistoryHint: TextView
    private lateinit var tvHistoryEmpty: TextView
    private lateinit var lvHistory: ListView

    // ---- Drawables ----
    private val blob1Bg = GradientDrawable().apply { shape = GradientDrawable.OVAL }
    private val blob2Bg = GradientDrawable().apply { shape = GradientDrawable.OVAL }
    private val cardBg = GradientDrawable()
    private val panelBg = GradientDrawable()
    private val cursorDrawable = GradientDrawable()
    private val titleBg = GradientDrawable()

    // ---- Estado ----
    private lateinit var prefs: SharedPreferences
    private var cur: Palette = Palette.PINK_LIGHT
    private var accent = Accent.PINK
    private var scientific = true
    private var dark = false
    private var deg = true
    private var soundOn = true
    private var justEvaluated = false
    private var lastResult: String? = null
    private var resultState = 0 // 0 = vista previa, 1 = final, 2 = error
    private var historyOpen = false
    private val history = ArrayList<HistoryItem>()
    private val keys = ArrayList<Key>()
    private var themeAnim: ValueAnimator? = null
    private lateinit var historyAdapter: HistoryAdapter
    private lateinit var backCallback: OnBackPressedCallback

    // ---- Sonido y sensores ----
    private var tone: ToneGenerator? = null
    private var sensorManager: SensorManager? = null
    private var accel: Sensor? = null
    private var px = 0f
    private var py = 0f

    private val sensorListener = object : SensorEventListener {
        override fun onSensorChanged(event: SensorEvent) {
            val tx = (-event.values[0] / 9.81f).coerceIn(-1f, 1f)
            val ty = (event.values[1] / 9.81f).coerceIn(-1f, 1f)
            px += (tx - px) * 0.08f
            py += (ty - py) * 0.08f
            blobTop.translationX = px * dpF(16)
            blobTop.translationY = py * dpF(16)
            blobBottom.translationX = -px * dpF(26)
            blobBottom.translationY = -py * dpF(26)
        }

        override fun onAccuracyChanged(sensor: Sensor?, accuracy: Int) {}
    }

    private val numberOnly = Regex("^[-−+]?[0-9.]*$")

    companion object {
        private const val PREFS = "calc_rosa_prefs"
        private const val K_DARK = "dark"
        private const val K_DEG = "deg"
        private const val K_SOUND = "sound"
        private const val K_ACCENT = "accent"
        private const val K_SCI = "scientific"
        private const val K_EXPR = "expr"
        private const val K_HISTORY = "history"
        private const val MAX_HISTORY = 200
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

        prefs = getSharedPreferences(PREFS, MODE_PRIVATE)
        bindViews()

        val systemDark = (resources.configuration.uiMode and Configuration.UI_MODE_NIGHT_MASK) ==
                Configuration.UI_MODE_NIGHT_YES
        dark = prefs.getBoolean(K_DARK, systemDark)
        deg = prefs.getBoolean(K_DEG, true)
        soundOn = prefs.getBoolean(K_SOUND, true)
        scientific = prefs.getBoolean(K_SCI, true)
        accent = Accent.values().getOrElse(prefs.getInt(K_ACCENT, Accent.PINK.ordinal)) { Accent.PINK }
        loadHistory()

        setupDrawables()
        setupKeys()
        setupHistoryUi()

        try {
            tone = ToneGenerator(AudioManager.STREAM_MUSIC, 80)
        } catch (e: Exception) {
            tone = null
        }
        sensorManager = getSystemService(SENSOR_SERVICE) as? SensorManager
        accel = sensorManager?.getDefaultSensor(Sensor.TYPE_ACCELEROMETER)

        // Pantalla de expresión: el cursor se puede mover y no aparece el teclado del sistema
        etExpression.showSoftInputOnFocus = false
        etExpression.setOnTouchListener { _, _ ->
            justEvaluated = false
            false
        }
        etExpression.requestFocus()

        cur = Palette.get(accent, dark)
        applyPalette(cur)
        updateSystemBars()
        refreshModeUi()
        adaptForOrientation()

        val saved = prefs.getString(K_EXPR, "") ?: ""
        etExpression.setText(saved)
        etExpression.setSelection(saved.length)
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

        backCallback = object : OnBackPressedCallback(false) {
            override fun handleOnBackPressed() {
                closeHistory()
            }
        }
        onBackPressedDispatcher.addCallback(this, backCallback)
    }

    override fun onResume() {
        super.onResume()
        val s = accel
        if (s != null && animationsEnabled()) {
            sensorManager?.registerListener(sensorListener, s, SensorManager.SENSOR_DELAY_UI)
        }
    }

    override fun onPause() {
        super.onPause()
        sensorManager?.unregisterListener(sensorListener)
        savePrefs()
    }

    override fun onDestroy() {
        super.onDestroy()
        themeAnim?.cancel()
        try {
            tone?.release()
        } catch (e: Exception) {
            // ignorar
        }
        tone = null
    }

    private fun savePrefs() {
        prefs.edit()
            .putBoolean(K_DARK, dark)
            .putBoolean(K_DEG, deg)
            .putBoolean(K_SOUND, soundOn)
            .putBoolean(K_SCI, scientific)
            .putInt(K_ACCENT, accent.ordinal)
            .putString(K_EXPR, etExpression.text.toString())
            .apply()
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
        btnMenu = findViewById(R.id.btnMenu)
        rowSci = findViewById(R.id.rowSci)
        historyPanel = findViewById(R.id.historyPanel)
        tvHistoryTitle = findViewById(R.id.tvHistoryTitle)
        tvHistoryHint = findViewById(R.id.tvHistoryHint)
        tvHistoryEmpty = findViewById(R.id.tvHistoryEmpty)
        lvHistory = findViewById(R.id.lvHistory)
    }

    private fun setupDrawables() {
        blobTop.background = blob1Bg
        blobBottom.background = blob2Bg
        cardBg.cornerRadius = dpF(22)
        displayCard.background = cardBg
        titleBg.cornerRadius = dpF(14)
        tvTitle.background = titleBg
        panelBg.cornerRadius = dpF(24)
        historyPanel.background = panelBg
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
            key(digitIds[d], Kind.NUM, ToneGenerator.TONE_DTMF_0 + d) { inputDigit(d.toString()) }
        }
        key(R.id.btnDot, Kind.NUM, ToneGenerator.TONE_DTMF_S) { inputDot() }

        // Operadores
        key(R.id.btnAdd, Kind.OP, ToneGenerator.TONE_DTMF_A) { inputOperator('+') }
        key(R.id.btnSubtract, Kind.OP, ToneGenerator.TONE_DTMF_A) { inputOperator('−') }
        key(R.id.btnMultiply, Kind.OP, ToneGenerator.TONE_DTMF_A) { inputOperator('×') }
        key(R.id.btnDivide, Kind.OP, ToneGenerator.TONE_DTMF_A) { inputOperator('÷') }

        // Funciones científicas y paréntesis
        key(R.id.btnSin, Kind.FUNC, ToneGenerator.TONE_DTMF_B) { inputFunction("sin") }
        key(R.id.btnCos, Kind.FUNC, ToneGenerator.TONE_DTMF_B) { inputFunction("cos") }
        key(R.id.btnTan, Kind.FUNC, ToneGenerator.TONE_DTMF_B) { inputFunction("tan") }
        key(R.id.btnOpen, Kind.FUNC, ToneGenerator.TONE_DTMF_C) { inputOpen() }
        key(R.id.btnClose, Kind.FUNC, ToneGenerator.TONE_DTMF_C) { inputClose() }
        key(R.id.btnPow, Kind.FUNC, ToneGenerator.TONE_DTMF_B) { inputOperator('^') }

        // Control
        key(R.id.btnClear, Kind.CLR, ToneGenerator.TONE_DTMF_D) { clearAll() }
        val back = key(R.id.btnBackspace, Kind.CLR, ToneGenerator.TONE_DTMF_D) { backspace() }
        back.setOnLongClickListener {
            clearAll()
            true
        }
        key(R.id.btnEquals, Kind.EQ, ToneGenerator.TONE_PROP_PROMPT) { calculate(true) }

        // Encabezado
        key(R.id.btnAngle, Kind.HDR, ToneGenerator.TONE_DTMF_C) { toggleAngle() }
        key(R.id.btnMenu, Kind.HDR, ToneGenerator.TONE_DTMF_C) { showMainMenu(btnMenu) }
        tvTitle.setOnClickListener {
            playTone(ToneGenerator.TONE_DTMF_C)
            showModePopup(tvTitle)
        }
    }

    private fun setupHistoryUi() {
        historyAdapter = HistoryAdapter()
        lvHistory.adapter = historyAdapter
        lvHistory.setOnItemClickListener { _, _, position, _ ->
            if (position in history.indices) {
                val e = history[position].expr
                justEvaluated = false
                etExpression.setText(e)
                etExpression.setSelection(e.length)
                closeHistory()
            }
        }
        key(R.id.btnClearHistory, Kind.HDR, -1) { confirmClearHistory() }
        key(R.id.btnCloseHistory, Kind.HDR, -1) { closeHistory() }
        updateHistoryEmpty()
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
    private fun key(id: Int, kind: Kind, toneType: Int, action: () -> Unit): Button {
        val b = findViewById<Button>(id)
        keys.add(Key(b, kind))
        b.setOnClickListener {
            playTone(toneType)
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

    private fun playTone(type: Int) {
        if (!soundOn || type < 0) return
        try {
            val t = tone
            if (t != null) {
                t.startTone(type, 45)
            } else {
                (getSystemService(AUDIO_SERVICE) as? AudioManager)?.playSoundEffect(AudioManager.FX_KEY_CLICK)
            }
        } catch (e: Exception) {
            // si el audio falla, la calculadora sigue funcionando
        }
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

    private fun calculate(addToHistory: Boolean) {
        val s = etExpression.text.toString().trim()
        if (s.isEmpty()) return
        try {
            val r = ExpressionEvaluator.format(ExpressionEvaluator.evaluate(s, deg))
            lastResult = r
            justEvaluated = true
            showResult(r, 1)
            animateResult()
            if (addToHistory && !numberOnly.matches(s)) addHistory(s, r)
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
        else -> if (dark) col("#FF8A9E") else col("#C62828")
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
        if (justEvaluated) calculate(false) else updatePreview()
        savePrefs()
    }

    private fun refreshAngleUi() {
        btnAngle.text = if (deg) "DEG" else "RAD"
        tvAngle.text = if (!scientific) "MODO BÁSICO" else if (deg) "DEG · GRADOS" else "RAD · RADIANES"
        btnAngle.contentDescription =
            if (deg) "Modo grados activo. Pulsa para usar radianes" else "Modo radianes activo. Pulsa para usar grados"
    }

    private fun toggleSound() {
        soundOn = !soundOn
        savePrefs()
        Toast.makeText(this, if (soundOn) "Sonido activado" else "Sonido desactivado", Toast.LENGTH_SHORT).show()
        if (soundOn) playTone(ToneGenerator.TONE_DTMF_C)
    }

    // =================================================================
    //  Historial
    // =================================================================

    private fun addHistory(expr: String, result: String) {
        val first = history.firstOrNull()
        if (first != null && first.expr == expr && first.result == result) return
        history.add(0, HistoryItem(expr, result))
        while (history.size > MAX_HISTORY) history.removeAt(history.lastIndex)
        saveHistory()
        historyAdapter.notifyDataSetChanged()
        updateHistoryEmpty()
    }

    private fun loadHistory() {
        history.clear()
        try {
            val arr = JSONArray(prefs.getString(K_HISTORY, "[]") ?: "[]")
            for (i in 0 until arr.length()) {
                val o = arr.getJSONObject(i)
                history.add(HistoryItem(o.getString("e"), o.getString("r")))
            }
        } catch (e: Exception) {
            history.clear()
        }
    }

    private fun saveHistory() {
        val arr = JSONArray()
        for (h in history) {
            arr.put(JSONObject().put("e", h.expr).put("r", h.result))
        }
        prefs.edit().putString(K_HISTORY, arr.toString()).apply()
    }

    private fun deleteHistoryAt(pos: Int) {
        if (pos !in history.indices) return
        history.removeAt(pos)
        saveHistory()
        historyAdapter.notifyDataSetChanged()
        updateHistoryEmpty()
    }

    private fun confirmClearHistory() {
        if (history.isEmpty()) return
        AlertDialog.Builder(this)
            .setTitle("Borrar historial")
            .setMessage("¿Eliminar todas las operaciones guardadas?")
            .setPositiveButton("Borrar") { _, _ ->
                history.clear()
                saveHistory()
                historyAdapter.notifyDataSetChanged()
                updateHistoryEmpty()
            }
            .setNegativeButton("Cancelar", null)
            .show()
    }

    private fun updateHistoryEmpty() {
        tvHistoryEmpty.visibility = if (history.isEmpty()) View.VISIBLE else View.GONE
    }

    private fun openHistory() {
        if (historyOpen) return
        historyOpen = true
        backCallback.isEnabled = true
        historyAdapter.notifyDataSetChanged()
        updateHistoryEmpty()
        historyPanel.visibility = View.VISIBLE
        if (animationsEnabled()) {
            historyPanel.alpha = 0f
            historyPanel.translationY = dpF(80)
            historyPanel.animate().alpha(1f).translationY(0f).setDuration(260)
                .setInterpolator(DecelerateInterpolator()).start()
        } else {
            historyPanel.alpha = 1f
            historyPanel.translationY = 0f
        }
    }

    private fun closeHistory() {
        if (!historyOpen) return
        historyOpen = false
        backCallback.isEnabled = false
        if (animationsEnabled()) {
            historyPanel.animate().alpha(0f).translationY(dpF(80)).setDuration(200)
                .withEndAction { if (!historyOpen) historyPanel.visibility = View.GONE }
                .start()
        } else {
            historyPanel.visibility = View.GONE
        }
    }

    private inner class HistoryAdapter : BaseAdapter() {
        override fun getCount() = history.size
        override fun getItem(position: Int): Any = history[position]
        override fun getItemId(position: Int) = position.toLong()

        override fun getView(position: Int, convertView: View?, parent: ViewGroup): View {
            val holder: HistoryHolder
            if (convertView == null) {
                holder = buildHolder()
                holder.row.tag = holder
            } else {
                holder = convertView.tag as HistoryHolder
            }
            val item = history[position]
            holder.pos = position
            holder.expr.text = item.expr
            holder.res.text = "= ${item.result}"
            holder.bg.setColor(cur.item)
            holder.bg.setStroke(dp(1), ColorUtils.setAlphaComponent(cur.stroke, 90))
            holder.expr.setTextColor(cur.textSec)
            holder.res.setTextColor(cur.text)
            holder.del.setTextColor(cur.clrText)
            return holder.row
        }

        private fun buildHolder(): HistoryHolder {
            val row = LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                setPadding(dp(14), dp(10), dp(6), dp(10))
                layoutParams = AbsListView.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT
                )
            }
            val bg = GradientDrawable().apply { cornerRadius = dpF(16) }
            row.background = bg

            val colLayout = LinearLayout(this@MainActivity).apply {
                orientation = LinearLayout.VERTICAL
            }
            val expr = TextView(this@MainActivity).apply { textSize = 14f }
            val res = TextView(this@MainActivity).apply {
                textSize = 20f
                setTypeface(typeface, android.graphics.Typeface.BOLD)
            }
            colLayout.addView(expr)
            colLayout.addView(res)
            row.addView(colLayout, LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f))

            val del = TextView(this@MainActivity).apply {
                text = "✕"
                textSize = 18f
                gravity = Gravity.CENTER
                isClickable = true
                contentDescription = "Borrar esta operación"
            }
            row.addView(del, LinearLayout.LayoutParams(dp(44), dp(44)))

            val holder = HistoryHolder(row, bg, expr, res, del)
            del.setOnClickListener { deleteHistoryAt(holder.pos) }
            return holder
        }
    }

    // =================================================================
    //  Temas, colores y animaciones
    // =================================================================

    private fun setTheme(toDark: Boolean, animate: Boolean) {
        dark = toDark
        applyTheme(animate)
    }

    private fun setAccent(a: Accent, animate: Boolean) {
        accent = a
        applyTheme(animate)
    }

    /** Aplica la combinación actual de color + modo claro/oscuro sin tocar la expresión. */
    private fun applyTheme(animate: Boolean) {
        val from = cur
        val to = Palette.get(accent, dark)
        updateSystemBars()
        themeAnim?.cancel()
        if (animate && animationsEnabled()) {
            val anim = ValueAnimator.ofFloat(0f, 1f)
            anim.duration = 350
            anim.addUpdateListener { applyPalette(Palette.lerp(from, to, it.animatedFraction)) }
            anim.addListener(object : AnimatorListenerAdapter() {
                override fun onAnimationEnd(animation: Animator) {
                    historyAdapter.notifyDataSetChanged()
                }
            })
            themeAnim = anim
            anim.start()
        } else {
            applyPalette(to)
            historyAdapter.notifyDataSetChanged()
        }
    }

    private fun setMode(sci: Boolean) {
        scientific = sci
        refreshModeUi()
        savePrefs()
    }

    private fun refreshModeUi() {
        tvTitle.text = if (scientific) "CALCULADORA CIENTÍFICA  ▾" else "CALCULADORA BÁSICA  ▾"
        tvTitle.contentDescription =
            if (scientific) "Calculadora científica. Pulsa para cambiar de tipo" else "Calculadora básica. Pulsa para cambiar de tipo"
        val vis = if (scientific) View.VISIBLE else View.GONE
        rowSci.visibility = vis
        btnAngle.visibility = vis
        refreshAngleUi()
    }

    private class Choice(val label: String, val dot: Int?, val selected: Boolean, val action: () -> Unit)

    /** Menú de tres puntos: sonido, modo claro/oscuro, colores e historial. */
    private fun showMainMenu(anchor: View) {
        showChoices(anchor, listOf(
            Choice(if (soundOn) "Sonido: activado" else "Sonido: desactivado", null, soundOn) {
                toggleSound()
            },
            Choice("Modo oscuro", null, dark) {
                playTone(ToneGenerator.TONE_DTMF_C)
                setTheme(!dark, true)
                savePrefs()
            },
            Choice("Cambiar colores  ▸", null, false) { showColorPopup(anchor) },
            Choice("Historial", null, false) { openHistory() }
        ), true)
    }

    private fun showModePopup(anchor: View) {
        showChoices(anchor, listOf(
            Choice("Calculadora científica", null, scientific) { setMode(true) },
            Choice("Calculadora básica", null, !scientific) { setMode(false) }
        ))
    }

    private fun showColorPopup(anchor: View) {
        showChoices(anchor, listOf(
            Choice("Azul", col("#2E7BFF"), accent == Accent.BLUE) {
                setAccent(Accent.BLUE, true)
                savePrefs()
            },
            Choice("Rosa fucsia", col("#FF2E93"), accent == Accent.PINK) {
                setAccent(Accent.PINK, true)
                savePrefs()
            },
            Choice("Verde", col("#14C46B"), accent == Accent.GREEN) {
                setAccent(Accent.GREEN, true)
                savePrefs()
            }
        ), true)
    }

    /** Menú desplegable propio, con los colores del tema actual. */
    private fun showChoices(anchor: View, choices: List<Choice>, alignEnd: Boolean = false) {
        val p = cur
        val ctx = this@MainActivity
        val box = LinearLayout(ctx).apply {
            orientation = LinearLayout.VERTICAL
            minimumWidth = dp(220)
            setPadding(dp(6), dp(6), dp(6), dp(6))
            background = GradientDrawable().apply {
                cornerRadius = dpF(16)
                setColor(p.card)
                setStroke(dp(1), ColorUtils.setAlphaComponent(p.stroke, 200))
            }
        }
        val popup = PopupWindow(
            box, ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT, true
        )
        popup.setBackgroundDrawable(ColorDrawable(Color.TRANSPARENT))
        popup.elevation = dpF(10)
        for (c in choices) {
            val row = LinearLayout(ctx).apply {
                orientation = LinearLayout.HORIZONTAL
                gravity = Gravity.CENTER_VERTICAL
                minimumHeight = dp(48)
                setPadding(dp(12), 0, dp(12), 0)
                isClickable = true
                contentDescription = c.label
                background = GradientDrawable().apply {
                    cornerRadius = dpF(12)
                    setColor(if (c.selected) p.hdrBg else Color.TRANSPARENT)
                }
            }
            val dotColor = c.dot
            if (dotColor != null) {
                row.addView(TextView(ctx).apply {
                    text = "●"
                    textSize = 20f
                    setTextColor(dotColor)
                    setPadding(0, 0, dp(10), 0)
                })
            }
            row.addView(
                TextView(ctx).apply {
                    text = c.label
                    textSize = 16f
                    setTextColor(p.text)
                },
                LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            )
            if (c.selected) {
                row.addView(TextView(ctx).apply {
                    text = "✓"
                    textSize = 18f
                    setTextColor(p.stroke)
                    setPadding(dp(10), 0, 0, 0)
                })
            }
            row.setOnClickListener {
                popup.dismiss()
                c.action()
            }
            box.addView(
                row,
                LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT)
            )
        }
        if (alignEnd) {
            popup.showAsDropDown(anchor, 0, dp(4), Gravity.END)
        } else {
            popup.showAsDropDown(anchor, 0, dp(4))
        }
    }

    private fun updateSystemBars() {
        val ctl = WindowCompat.getInsetsController(window, root)
        ctl.isAppearanceLightStatusBars = !dark
        ctl.isAppearanceLightNavigationBars = !dark
    }

    private fun applyPalette(p: Palette) {
        cur = p
        root.setBackgroundColor(p.bg)
        window.decorView.setBackgroundColor(p.bg)
        blob1Bg.setColor(p.blob1)
        blob2Bg.setColor(p.blob2)

        cardBg.setColor(p.card)
        cardBg.setStroke(dp(2), p.stroke)
        panelBg.setColor(p.panel)
        panelBg.setStroke(dp(2), ColorUtils.setAlphaComponent(p.stroke, 200))
        cursorDrawable.setColor(p.stroke)

        tvTitle.setTextColor(p.text)
        titleBg.setColor(p.hdrBg)
        titleBg.setStroke(dp(1), ColorUtils.setAlphaComponent(p.stroke, 140))
        tvTitle.setShadowLayer(16f, 0f, 0f, ColorUtils.setAlphaComponent(p.stroke, 150))
        tvAngle.setTextColor(p.funcText)
        etExpression.setTextColor(p.text)
        etExpression.setHintTextColor(p.textSec)
        tvResult.setTextColor(resultColor())

        tvHistoryTitle.setTextColor(p.text)
        tvHistoryHint.setTextColor(p.textSec)
        tvHistoryEmpty.setTextColor(p.textSec)

        for (k in keys) k.refresh(p)
    }

    private fun adaptForOrientation() {
        if (resources.configuration.orientation == Configuration.ORIENTATION_LANDSCAPE) {
            val m = dp(2)
            for (k in keys) {
                if (k.kind == Kind.HDR) continue
                k.view.textSize = 16f
                (k.view.layoutParams as? LinearLayout.LayoutParams)?.setMargins(m, m, m, m)
                k.view.requestLayout()
            }
            etExpression.textSize = 22f
        }
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