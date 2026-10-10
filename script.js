/* ==========================================================================
   PRISM — scientific calculator
   1. Engine: tokenizer -> recursive-descent parser -> AST -> evaluator
      (no eval(), no new Function())
   2. Input model: edits an expression string, one key at a time
   3. Interface: rendering, tape (history), keyboard, preferences
   ========================================================================== */
(() => {
  'use strict';

  /* ======================================================================
     1. ENGINE
     ====================================================================== */

  class CalcError extends Error {}

  const OPMAP = {
    '+': '+', '-': '-', '\u2212': '-', '\u2013': '-',
    '*': '*', '\u00D7': '*', '\u00B7': '*',
    '/': '/', '\u00F7': '/',
    '^': '^'
  };
  const OP_SHOWN = { '+': '+', '-': '\u2212', '*': '\u00D7', '/': '\u00F7', '^': '^' };

  // Longest names first so "asin" wins over "sin", "sinh" over "sin", etc.
  const NAMED = [
    ['asin', 'fn', 'asin'], ['acos', 'fn', 'acos'], ['atan', 'fn', 'atan'],
    ['sinh', 'fn', 'sinh'], ['cosh', 'fn', 'cosh'], ['tanh', 'fn', 'tanh'],
    ['sqrt', 'fn', 'sqrt'], ['cbrt', 'fn', 'cbrt'],
    ['sin', 'fn', 'sin'], ['cos', 'fn', 'cos'], ['tan', 'fn', 'tan'],
    ['log', 'fn', 'log'], ['abs', 'fn', 'abs'], ['ln', 'fn', 'ln'],
    ['\u221A', 'fn', 'sqrt'], ['\u221B', 'fn', 'cbrt'],
    ['Ans', 'const', 'ans'], ['pi', 'const', 'pi'], ['\u03C0', 'const', 'pi'],
    ['e', 'const', 'e']
  ];

  function tokenize(src) {
    const out = [];
    let i = 0;
    while (i < src.length) {
      const ch = src[i];
      if (ch === ' ' || ch === '\u00A0') { i++; continue; }

      if (/[0-9.]/.test(ch)) {
        const m = /^(?:\d+\.?\d*|\.\d+)(?:E[+\-\u2212]?\d+)?/.exec(src.slice(i));
        if (!m) throw new CalcError('Misplaced decimal point');
        i += m[0].length;
        if (src[i] === '.') throw new CalcError('A number cannot have two decimal points');
        out.push({ type: 'num', value: parseFloat(m[0].replace('\u2212', '-')) });
        continue;
      }

      if (OPMAP[ch]) { out.push({ type: 'op', value: OPMAP[ch] }); i++; continue; }
      if (ch === '(') { out.push({ type: 'lp' }); i++; continue; }
      if (ch === ')') { out.push({ type: 'rp' }); i++; continue; }
      if (ch === '!' || ch === '%') { out.push({ type: 'post', value: ch }); i++; continue; }

      let matched = false;
      for (const [name, type, value] of NAMED) {
        if (src.startsWith(name, i)) {
          out.push({ type, value });
          i += name.length;
          matched = true;
          break;
        }
      }
      if (!matched) throw new CalcError('Unknown symbol \u201C' + ch + '\u201D');
    }
    return out;
  }

  /*  Grammar (lowest to highest precedence)
        expression := term (('+' | '-') term)*
        term       := unary (('*' | '/') unary | implicit-multiply unary)*
        unary      := ('-' | '+') unary | power
        power      := postfix ('^' unary)?          right-associative
        postfix    := primary ('!' | '%')*
        primary    := number | constant | name '(' expression ')' | '(' expression ')'
     So -2^2 = -4, 2^-1 = 0.5, 2^3! = 2^6, and 2^3^2 = 2^9.               */
  function parse(tokens) {
    let p = 0;
    const peek = () => tokens[p];
    const take = () => tokens[p++];
    const isOp = (t, ...vals) => !!t && t.type === 'op' && vals.includes(t.value);
    const startsPrimary = t => !!t && (t.type === 'num' || t.type === 'const' || t.type === 'fn' || t.type === 'lp');

    function expectClose() {
      const t = take();
      if (!t || t.type !== 'rp') throw new CalcError('Missing closing parenthesis )');
    }

    function expression() {
      let node = term();
      while (isOp(peek(), '+', '-')) {
        const op = take().value;
        node = { t: 'bin', op, l: node, r: term() };
      }
      return node;
    }

    function term() {
      let node = unary();
      for (;;) {
        const t = peek();
        if (isOp(t, '*', '/')) {
          take();
          node = { t: 'bin', op: t.value, l: node, r: unary() };
        } else if (startsPrimary(t)) {
          node = { t: 'bin', op: '*', l: node, r: unary() };   // 2π, 3(4), (1)(2)
        } else {
          break;
        }
      }
      return node;
    }

    function unary() {
      if (isOp(peek(), '-')) { take(); return { t: 'neg', x: unary() }; }
      if (isOp(peek(), '+')) { take(); return unary(); }
      return power();
    }

    function power() {
      const base = postfix();
      if (isOp(peek(), '^')) {
        take();
        return { t: 'pow', l: base, r: unary() };
      }
      return base;
    }

    function postfix() {
      let node = primary();
      while (peek() && peek().type === 'post') {
        const v = take().value;
        node = { t: v === '!' ? 'fact' : 'pct', x: node };
      }
      return node;
    }

    function primary() {
      const t = take();
      if (!t) throw new CalcError('The expression is incomplete');
      switch (t.type) {
        case 'num': return { t: 'num', v: t.value };
        case 'const': return { t: 'const', name: t.value };
        case 'fn': {
          const open = take();
          if (!open || open.type !== 'lp') throw new CalcError('A function needs brackets, like sin(30)');
          if (peek() && peek().type === 'rp') throw new CalcError('Nothing inside the brackets');
          const x = expression();
          expectClose();
          return { t: 'fn', name: t.value, x };
        }
        case 'lp': {
          if (peek() && peek().type === 'rp') throw new CalcError('Nothing inside the brackets');
          const x = expression();
          expectClose();
          return { t: 'group', x };
        }
        case 'rp': throw new CalcError('Unexpected closing parenthesis )');
        case 'op': throw new CalcError('A number is missing before or after \u201C' + OP_SHOWN[t.value] + '\u201D');
        case 'post': throw new CalcError('Nothing to apply \u201C' + t.value + '\u201D to');
        default: throw new CalcError('Unexpected input');
      }
    }

    const ast = expression();
    if (p < tokens.length) {
      throw new CalcError(tokens[p].type === 'rp'
        ? 'Unexpected closing parenthesis )'
        : 'Unexpected input after the expression');
    }
    return ast;
  }

  const tidy = x => Number(x.toPrecision(15));   // removes float noise: 0.1+0.2 -> 0.3

  function factorial(n) {
    if (Math.abs(n - Math.round(n)) > 1e-12 || n < -1e-12) {
      throw new CalcError('Factorial needs a whole number \u2265 0');
    }
    n = Math.round(n);
    if (n > 170) throw new CalcError('Factorial is too large (170! is the maximum)');
    let r = 1;
    for (let i = 2; i <= n; i++) r *= i;
    return r;
  }

  function power(b, e) {
    if (b === 0 && e < 0) throw new CalcError('Cannot divide by zero');
    if (b < 0 && !Number.isInteger(e)) {
      const inv = 1 / e;
      const r = Math.round(inv);
      if (Math.abs(inv - r) < 1e-9 && r % 2 !== 0) return -Math.pow(-b, e);   // real odd roots, e.g. (-8)^(1/3)
      throw new CalcError('A negative number has no real fractional power');
    }
    return Math.pow(b, e);
  }

  function trig(name, x, deg) {
    if (deg) {
      const a = ((x % 360) + 360) % 360;
      if (name === 'sin') {
        if (a % 180 === 0) return 0;
        if (a === 90) return 1;
        if (a === 270) return -1;
      } else if (name === 'cos') {
        if (a === 90 || a === 270) return 0;
        if (a === 0) return 1;
        if (a === 180) return -1;
      } else {
        const m = a % 180;
        if (m === 0) return 0;
        if (m === 90) throw new CalcError('tan is undefined at this angle');
      }
      x = x * Math.PI / 180;
    }
    let v;
    if (name === 'sin') v = Math.sin(x);
    else if (name === 'cos') v = Math.cos(x);
    else {
      if (Math.abs(Math.cos(x)) < 1e-15) throw new CalcError('tan is undefined at this angle');
      v = Math.tan(x);
    }
    if (Math.abs(v) < 1e-15 && Math.abs(x) > 1e-5) v = 0;   // sin(pi) is 0, not 1.2e-16
    return v;
  }

  function applyFn(name, x, angle) {
    const deg = angle === 'DEG';
    switch (name) {
      case 'sin': case 'cos': case 'tan': return trig(name, x, deg);
      case 'asin': case 'acos': {
        if (Math.abs(x) > 1 + 1e-12) throw new CalcError(name + ' needs a value from \u22121 to 1');
        const c = Math.max(-1, Math.min(1, x));
        const v = name === 'asin' ? Math.asin(c) : Math.acos(c);
        return deg ? v * 180 / Math.PI : v;
      }
      case 'atan': {
        const v = Math.atan(x);
        return deg ? v * 180 / Math.PI : v;
      }
      case 'sinh': return Math.sinh(x);
      case 'cosh': return Math.cosh(x);
      case 'tanh': return Math.tanh(x);
      case 'log':
        if (x <= 0) throw new CalcError('log needs a number greater than 0');
        return Math.log10(x);
      case 'ln':
        if (x <= 0) throw new CalcError('ln needs a number greater than 0');
        return Math.log(x);
      case 'sqrt':
        if (x < 0) throw new CalcError('\u221A needs a number \u2265 0');
        return Math.sqrt(x);
      case 'cbrt': return Math.cbrt(x);
      case 'abs': return Math.abs(x);
      default: throw new CalcError('Unknown function');
    }
  }

  function ev(node, ctx) {
    const v = evalNode(node, ctx);
    if (Number.isNaN(v)) throw new CalcError('The result is not a real number');
    if (!Number.isFinite(v)) throw new CalcError('The result is too large');
    return v;
  }

  function evalNode(node, ctx) {
    switch (node.t) {
      case 'num': return node.v;
      case 'const':
        if (node.name === 'pi') return Math.PI;
        if (node.name === 'e') return Math.E;
        return ctx.ans;
      case 'group': return ev(node.x, ctx);
      case 'neg': return -ev(node.x, ctx);
      case 'pct': return ev(node.x, ctx) / 100;
      case 'fact': return factorial(ev(node.x, ctx));
      case 'pow': return power(ev(node.l, ctx), ev(node.r, ctx));
      case 'fn': return applyFn(node.name, ev(node.x, ctx), ctx.angle);
      case 'bin': {
        const l = ev(node.l, ctx);
        // "200 + 10%" means 200 + 10% of 200
        if ((node.op === '+' || node.op === '-') && node.r.t === 'pct') {
          const part = l * ev(node.r.x, ctx) / 100;
          return tidy(node.op === '+' ? l + part : l - part);
        }
        const r = ev(node.r, ctx);
        switch (node.op) {
          case '+': return tidy(l + r);
          case '-': return tidy(l - r);
          case '*': return l * r;
          default:
            if (r === 0) throw new CalcError('Cannot divide by zero');
            return l / r;
        }
      }
      default: throw new CalcError('Unexpected input');
    }
  }

  function calculate(src, ctx) {
    try {
      const tokens = tokenize(src);
      if (!tokens.length) throw new CalcError('Nothing to calculate');
      let v = tidy(ev(parse(tokens), ctx));
      if (Object.is(v, -0)) v = 0;
      return v;
    } catch (err) {
      if (err instanceof RangeError) throw new CalcError('That expression is too deeply nested');
      throw err;
    }
  }

  /* Number formatting. Minus is U+2212; exponents print as a×10^n. */
  function fmt(v, digits = 12) {
    if (v === 0 || Object.is(v, -0)) return '0';
    const abs = Math.abs(v);
    let s;
    if (Number.isInteger(v) && abs < 1e15) {
      s = String(v);
    } else if (abs >= 1e15 || abs < 1e-6) {
      const [m0, e0] = v.toExponential(digits - 1).split('e');
      const m = m0.includes('.') ? m0.replace(/\.?0+$/, '') : m0;
      const ex = parseInt(e0, 10);
      s = m + '\u00D710^' + (ex < 0 ? '-' : '') + Math.abs(ex);
    } else {
      s = String(Number(v.toPrecision(digits)));
    }
    return s.replace(/-/g, '\u2212');
  }

  /* ======================================================================
     2. INPUT MODEL
     ====================================================================== */

  const OPS = '+\u2212\u00D7\u00F7^';
  const MAX_LEN = 220;
  const NAME_END = '(?:asin|acos|atan|sinh|cosh|tanh|sin|cos|tan|log|ln|abs|\u221A|\u221B)';
  const FN_END = new RegExp(NAME_END + '\\($');
  const FN_BEFORE_PAREN = new RegExp(NAME_END + '$');
  const OPERAND_END = /[0-9.)\u03C0es!%]$/;      // digit . ) π e (Ans ends in s) ! %
  const PLAIN_NUMBER = /^\u2212?[0-9]*\.?[0-9]*$/;
  const TRIG_WORDS = /sin|cos|tan/;

  const state = {
    expr: '',
    done: false,
    error: null,
    value: 0,
    ans: 0,
    angle: 'DEG',
    history: []
  };

  const isOpChar = c => c !== '' && OPS.includes(c);
  const ctx = () => ({ angle: state.angle, ans: state.ans });

  function closeParens(e) {
    let open = 0;
    for (const c of e) {
      if (c === '(') open++;
      else if (c === ')') open--;
    }
    return open > 0 ? e + ')'.repeat(open) : e;
  }

  function openCount(e) {
    let open = 0;
    for (const c of e) {
      if (c === '(') open++;
      else if (c === ')') open--;
    }
    return open;
  }

  function wrapForPostfix(s) {
    return (s.includes('\u00D7') || s.startsWith('\u2212')) ? '(' + s + ')' : s;
  }

  /* Called before every edit: clears errors and, after "=", either starts
     fresh (new value) or continues from the result (operator / postfix / sign). */
  function beforeInput(kind, sym) {
    state.error = null;
    if (!state.done) return;
    state.done = false;
    if (kind === 'value') { state.expr = ''; return; }
    let s = fmt(state.value, 15);
    if (kind === 'post' || sym === '^') s = wrapForPostfix(s);
    state.expr = s;
  }

  function append(text) {
    if (state.expr.length + text.length > MAX_LEN) return false;
    state.expr += text;
    return true;
  }

  // A number or "1/x"-style text must not fuse with digits before it.
  function appendValueText(text) {
    if (/[0-9.]$/.test(state.expr) && /^[0-9.]/.test(text)) text = '\u00D7' + text;
    return append(text);
  }

  function trailingNumber(e) {
    return /(\d*\.?\d*)$/.exec(e)[1];
  }

  function inputDigit(d) {
    beforeInput('value');
    const run = trailingNumber(state.expr);
    if (run === '0') {
      if (d === '0') return;
      state.expr = state.expr.slice(0, -1) + d;
      return;
    }
    if (run.replace('.', '').length >= 15) return;
    append(d);
  }

  function inputDot() {
    beforeInput('value');
    const run = trailingNumber(state.expr);
    if (run.includes('.')) return;
    if (run === '') appendValueText('0.');
    else append('.');
  }

  function inputOp(op) {
    beforeInput('op', op);
    const e = state.expr;
    const last = e.slice(-1);

    if (e === '') { if (op === '\u2212') append('\u2212'); return; }

    if (last === '(') { if (op === '\u2212') append('\u2212'); return; }

    if (isOpChar(last)) {
      if (op === '\u2212' && '\u00D7\u00F7^'.includes(last)) { append('\u2212'); return; }  // 5×−3, 2^−1
      let t = e;
      while (isOpChar(t.slice(-1))) t = t.slice(0, -1);
      if (t === '' || t.slice(-1) === '(') {
        state.expr = op === '\u2212' ? t + '\u2212' : t;
        return;
      }
      state.expr = t + op;
      return;
    }
    append(op);
  }

  function inputParen(p) {
    if (p === '(') {
      beforeInput('value');
      append('(');
      return;
    }
    if (state.done) return;
    state.error = null;
    const last = state.expr.slice(-1);
    if (openCount(state.expr) > 0 && last !== '(' && !isOpChar(last) && last !== '') append(')');
  }

  function inputFn(name) {
    beforeInput('value');
    append(name + '(');
  }

  function inputConst(c) {
    beforeInput('value');
    append(c);
  }

  function inputPost(sym) {
    beforeInput('post', sym);
    if (OPERAND_END.test(state.expr)) append(sym);
  }

  function inputPow2() {
    beforeInput('post', '^');
    if (OPERAND_END.test(state.expr)) append('^2');
  }

  function inputRecip() {
    beforeInput('post', '^');
    if (OPERAND_END.test(state.expr)) append('^\u22121');
  }

  function inputTenPow() { beforeInput('value'); appendValueText('10^('); }
  function inputExpPow() { beforeInput('value'); append('e^('); }

  function matchingParenEnd(s, start) {
    let depth = 0;
    for (let i = start; i < s.length; i++) {
      if (s[i] === '(') depth++;
      else if (s[i] === ')') { depth--; if (depth === 0) return i; }
    }
    return -1;
  }

  /* Where does the operand at the end of the expression begin? (-1 if none) */
  function operandStart(e) {
    let end = e.length;
    while (end > 0 && '!%'.includes(e[end - 1])) end--;
    if (end === 0) return -1;
    const c = e[end - 1];
    if (c === ')') {
      let depth = 0;
      for (let i = end - 1; i >= 0; i--) {
        if (e[i] === ')') depth++;
        else if (e[i] === '(') {
          depth--;
          if (depth === 0) {
            const m = FN_BEFORE_PAREN.exec(e.slice(0, i));
            return m ? i - m[0].length : i;
          }
        }
      }
      return -1;
    }
    if (/[0-9.]/.test(c)) {
      let i = end;
      while (i > 0 && /[0-9.]/.test(e[i - 1])) i--;
      return i;
    }
    if (c === '\u03C0' || c === 'e') return end - 1;
    if (c === 's' && e.slice(end - 3, end) === 'Ans') return end - 3;
    return -1;
  }

  function toggleSign() {
    state.error = null;
    if (state.done) { state.done = false; state.expr = fmt(state.value, 15); }

    const e = state.expr;
    const s = operandStart(e);

    if (s < 0) {
      const last = e.slice(-1);
      if (e === '' || '(\u00D7\u00F7^+'.includes(last)) { append('\u2212'); return; }
      if (last === '\u2212') {
        const prev = e.slice(-2, -1);
        if (prev === '' || '(\u00D7\u00F7^+'.includes(prev)) state.expr = e.slice(0, -1);
      }
      return;
    }

    const operand = e.slice(s);
    const before = e.slice(0, s);

    // "(−x)" -> "x"
    if (operand.startsWith('(\u2212') && matchingParenEnd(operand, 0) === operand.length - 1) {
      state.expr = before + operand.slice(2, -1);
      return;
    }

    const prev = before.slice(-1);
    if (prev === '\u2212') {
      const pp = before.slice(-2, -1);
      if (pp === '' || '(\u00D7\u00F7^+\u2212'.includes(pp)) state.expr = before.slice(0, -1) + operand;   // unary minus off
      else state.expr = before.slice(0, -1) + '+' + operand;                                             // 3−5 -> 3+5
      return;
    }
    if (prev === '+') { state.expr = before.slice(0, -1) + '\u2212' + operand; return; }
    if (before === '' || '(\u00D7\u00F7^'.includes(prev)) { state.expr = before + '\u2212' + operand; return; }
    state.expr = before + '(\u2212' + operand + ')';                                                      // 2π -> 2(−π)
  }

  function backspace() {
    state.error = null;
    state.done = false;
    const e = state.expr;
    if (e.endsWith('Ans')) { state.expr = e.slice(0, -3); return; }
    const m = FN_END.exec(e);
    state.expr = m ? e.slice(0, -m[0].length) : e.slice(0, -1);
  }

  function clearAll() {
    state.expr = '';
    state.done = false;
    state.error = null;
  }

  function equals() {
    if (state.done || state.expr === '') return;
    const closed = closeParens(state.expr);
    try {
      const v = calculate(closed, ctx());
      state.expr = closed;
      state.value = v;
      state.ans = v;
      state.done = true;
      state.error = null;
      pushHistory(closed, v);
      fanStrip();
      announce(closed + ' equals ' + fmt(v));
    } catch (err) {
      if (!(err instanceof CalcError)) throw err;
      state.error = err.message;
      announce('Error: ' + err.message);
    }
  }

  function setAngle(mode) {
    if (mode !== 'DEG' && mode !== 'RAD') return;
    state.angle = mode;
    savePrefs();
    renderMode();
  }

  /* Live preview: drop any dangling operator or function opener, close brackets. */
  function previewValue() {
    let e = state.expr;
    for (;;) {
      if (isOpChar(e.slice(-1))) { e = e.slice(0, -1); continue; }
      const m = FN_END.exec(e);
      if (m) { e = e.slice(0, -m[0].length); continue; }
      if (e.endsWith('(')) { e = e.slice(0, -1); continue; }
      break;
    }
    if (!e) return null;
    try {
      return calculate(closeParens(e), ctx());
    } catch (err) {
      if (err instanceof CalcError) return null;
      throw err;
    }
  }

  /* ======================================================================
     3. INTERFACE
     ====================================================================== */

  const $ = id => document.getElementById(id);
  const app = $('app');
  const exprEl = $('expr');
  const resultEl = $('result');
  const stripEl = $('strip');
  const modeTag = $('mode-tag');
  const statusEl = $('sr-status');
  const btnSci = $('btn-sci');
  const btnTape = $('btn-tape');
  const btnClearTape = $('btn-clear-tape');
  const tapeList = $('tape-list');
  const tapeEmpty = $('tape-empty');
  const keysEl = document.querySelector('.keys');
  const keyButtons = Array.from(document.querySelectorAll('[data-act]'));
  const desktopMQ = window.matchMedia('(min-width: 1020px)');
  const phoneMQ = window.matchMedia('(max-width: 639px)');

  const store = {
    get(key) { try { return JSON.parse(window.localStorage.getItem(key)); } catch (e) { return null; } },
    set(key, val) { try { window.localStorage.setItem(key, JSON.stringify(val)); } catch (e) { /* storage unavailable */ } }
  };
  const HIST_KEY = 'prism.tape.v1';
  const PREF_KEY = 'prism.prefs.v1';
  const MAX_HISTORY = 60;

  /* ---- number rendering (a×10^n gets a real superscript) ---- */
  function fillNumber(el, text) {
    el.textContent = '';
    const i = text.indexOf('\u00D710^');
    if (i === -1) { el.textContent = text; return; }
    el.append(text.slice(0, i + 3));
    const sup = document.createElement('sup');
    sup.textContent = text.slice(i + 4);
    el.append(sup);
  }

  function fitResult() {
    resultEl.style.fontSize = '';
    if (resultEl.classList.contains('is-error')) return;
    let size = parseFloat(window.getComputedStyle(resultEl).fontSize) || 60;
    while (resultEl.scrollWidth > resultEl.clientWidth && size > 18) {
      size -= 2;
      resultEl.style.fontSize = size + 'px';
    }
  }

  function announce(msg) { statusEl.textContent = msg; }

  function fanStrip() {
    stripEl.classList.remove('is-fan');
    void stripEl.offsetWidth;      // restart the animation
    stripEl.classList.add('is-fan');
  }

  function render() {
    const e = state.expr;
    exprEl.textContent = e ? e + (state.done ? ' =' : '') : '\u00A0';
    exprEl.scrollLeft = exprEl.scrollWidth;

    resultEl.classList.remove('is-error', 'is-preview');
    stripEl.classList.toggle('is-error', !!state.error);

    if (state.error) {
      resultEl.classList.add('is-error');
      resultEl.textContent = state.error;
    } else if (state.done) {
      fillNumber(resultEl, fmt(state.value));
    } else if (e === '') {
      resultEl.textContent = '0';
    } else if (PLAIN_NUMBER.test(e)) {
      resultEl.textContent = e;
    } else {
      const v = previewValue();
      resultEl.classList.add('is-preview');
      if (v === null) resultEl.textContent = '\u00A0';
      else fillNumber(resultEl, fmt(v));
    }
    fitResult();
  }

  function renderMode() {
    modeTag.textContent = state.angle;
    document.querySelectorAll('.seg-btn').forEach(b => {
      b.setAttribute('aria-pressed', String(b.dataset.val === state.angle));
    });
    render();
  }

  /* ---- panels ---- */
  function setSci(on) {
    app.classList.toggle('is-basic', !on);
    btnSci.setAttribute('aria-expanded', String(on));
    savePrefs();
    fitResult();
  }
  const sciOn = () => !app.classList.contains('is-basic');

  function setTape(open) {
    app.classList.toggle('tape-open', open);
    btnTape.setAttribute('aria-expanded', String(open));
  }
  const tapeOpen = () => app.classList.contains('tape-open');

  function savePrefs() { store.set(PREF_KEY, { angle: state.angle, sci: sciOn() }); }

  /* ---- tape ---- */
  function pushHistory(expr, value) {
    state.history.unshift({ expr, value, angle: state.angle });
    if (state.history.length > MAX_HISTORY) state.history.length = MAX_HISTORY;
    store.set(HIST_KEY, state.history);
    renderTape();
  }

  function renderTape() {
    tapeList.textContent = '';
    tapeEmpty.hidden = state.history.length > 0;
    btnClearTape.hidden = state.history.length === 0;
    state.history.forEach((h, i) => {
      const li = document.createElement('li');
      li.className = 'tape-item';
      li.dataset.index = String(i);

      const bExpr = document.createElement('button');
      bExpr.type = 'button';
      bExpr.className = 'tape-expr';
      bExpr.dataset.use = 'expr';
      bExpr.title = 'Edit this expression';
      bExpr.append(h.expr + ' =');
      if (TRIG_WORDS.test(h.expr)) {
        const tag = document.createElement('span');
        tag.className = 'tape-tag';
        tag.textContent = h.angle;
        bExpr.append(tag);
      }

      const bRes = document.createElement('button');
      bRes.type = 'button';
      bRes.className = 'tape-res';
      bRes.dataset.use = 'result';
      bRes.title = 'Use this result';
      fillNumber(bRes, fmt(h.value));

      li.append(bExpr, bRes);
      tapeList.append(li);
    });
  }

  function loadHistory() {
    const saved = store.get(HIST_KEY);
    if (!Array.isArray(saved)) return;
    state.history = saved
      .filter(h => h && typeof h.expr === 'string' && Number.isFinite(h.value))
      .slice(0, MAX_HISTORY)
      .map(h => ({ expr: h.expr, value: h.value, angle: h.angle === 'RAD' ? 'RAD' : 'DEG' }));
    if (state.history.length) state.ans = state.history[0].value;
  }

  function insertNumber(v) {
    let s = fmt(v, 15);
    const needsWrap = s.includes('\u00D7') || (v < 0 && state.expr !== '' && state.expr.slice(-1) !== '(');
    if (needsWrap) s = '(' + s + ')';
    appendValueText(s);
  }

  tapeList.addEventListener('click', ev => {
    const b = ev.target.closest('button[data-use]');
    if (!b) return;
    const h = state.history[Number(b.closest('li').dataset.index)];
    if (!h) return;
    if (b.dataset.use === 'expr') {
      state.expr = h.expr;
      state.done = false;
      state.error = null;
    } else {
      beforeInput('value');
      insertNumber(h.value);
    }
    render();
    if (!desktopMQ.matches) setTape(false);
  });

  btnClearTape.addEventListener('click', () => {
    state.history = [];
    store.set(HIST_KEY, state.history);
    renderTape();
    announce('Tape cleared');
  });

  /* ---- key dispatch ---- */
  function press(act, val) {
    switch (act) {
      case 'digit': inputDigit(val); break;
      case 'dot': inputDot(); break;
      case 'op': inputOp(val); break;
      case 'paren': inputParen(val); break;
      case 'fn': inputFn(val); break;
      case 'const': inputConst(val); break;
      case 'post': inputPost(val); break;
      case 'pow2': inputPow2(); break;
      case 'recip': inputRecip(); break;
      case 'tenpow': inputTenPow(); break;
      case 'exppow': inputExpPow(); break;
      case 'sign': toggleSign(); break;
      case 'back': backspace(); break;
      case 'clear': clearAll(); break;
      case 'equals': equals(); break;
      case 'angle': setAngle(val); return;
      default: return;
    }
    render();
  }

  keysEl.addEventListener('click', ev => {
    const btn = ev.target.closest('button[data-act]');
    if (!btn) return;
    press(btn.dataset.act, btn.dataset.val);
    if (ev.detail > 0) btn.blur();      // pointer click: keep the keyboard free for typing
  });

  btnSci.addEventListener('click', () => setSci(!sciOn()));
  btnTape.addEventListener('click', () => setTape(!tapeOpen()));

  /* ---- keyboard ---- */
  function flash(act, val) {
    const btn = keyButtons.find(b => b.dataset.act === act && (b.dataset.val || '') === (val || ''));
    if (!btn) return;
    btn.classList.add('is-hit');
    window.setTimeout(() => btn.classList.remove('is-hit'), 130);
  }

  function keyPress(act, val) {
    flash(act, val);
    press(act, val);
  }

  document.addEventListener('keydown', ev => {
    if (ev.ctrlKey || ev.metaKey || ev.altKey) return;
    const k = ev.key;
    const onButton = ev.target instanceof Element && ev.target.closest('button');
    if (onButton && (k === 'Enter' || k === ' ')) return;     // let focused controls activate normally

    let handled = true;
    if (/^[0-9]$/.test(k)) keyPress('digit', k);
    else {
      switch (k) {
        case '.': case ',': keyPress('dot'); break;
        case '+': keyPress('op', '+'); break;
        case '-': keyPress('op', '\u2212'); break;
        case '*': case 'x': case 'X': keyPress('op', '\u00D7'); break;
        case '/': keyPress('op', '\u00F7'); break;
        case '^': keyPress('op', '^'); break;
        case '(': keyPress('paren', '('); break;
        case ')': keyPress('paren', ')'); break;
        case '!': keyPress('post', '!'); break;
        case '%': keyPress('post', '%'); break;
        case 'Enter': case '=': keyPress('equals'); break;
        case 'Backspace': keyPress('back'); break;
        case 'Delete': keyPress('clear'); break;
        case 'Escape':
          if (tapeOpen() && !desktopMQ.matches) setTape(false);
          else keyPress('clear');
          break;
        case 's': keyPress('fn', 'sin'); break;
        case 'c': keyPress('fn', 'cos'); break;
        case 't': keyPress('fn', 'tan'); break;
        case 'S': keyPress('fn', 'asin'); break;
        case 'C': keyPress('fn', 'acos'); break;
        case 'T': keyPress('fn', 'atan'); break;
        case 'l': keyPress('fn', 'log'); break;
        case 'n': keyPress('fn', 'ln'); break;
        case 'r': keyPress('fn', '\u221A'); break;
        case 'p': keyPress('const', '\u03C0'); break;
        case 'e': keyPress('const', 'e'); break;
        case 'a': keyPress('const', 'Ans'); break;
        case 'q': keyPress('pow2'); break;
        case 'f': keyPress('post', '!'); break;
        case 'd': keyPress('angle', state.angle === 'DEG' ? 'RAD' : 'DEG'); break;
        case 'h': setTape(!tapeOpen()); break;
        default: handled = false;
      }
    }
    if (handled) ev.preventDefault();
  });

  window.addEventListener('resize', fitResult);
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(fitResult);

  /* ---- boot ---- */
  (function init() {
    const prefs = store.get(PREF_KEY);
    if (prefs && (prefs.angle === 'DEG' || prefs.angle === 'RAD')) state.angle = prefs.angle;
    const wantSci = prefs && typeof prefs.sci === 'boolean' ? prefs.sci : !phoneMQ.matches;
    loadHistory();
    renderTape();
    setSci(wantSci);
    setTape(false);
    renderMode();
  })();
})();