var app = new Vue({
    el: '#app',

    // DATA OBJECT
    data: {
        mode: 'number',
        decimal: false,
        numberInput: '',
        algebraInput: '',
        // Simply store user inputs, for scrolling up/down
        numberInputStored: [],
        numberInputStoredIndex: -1,
        numberInputTmp: '',
        algebraInputStored: [],
        algebraInputStoredIndex: -1,
        algebraInputTmp: '',
        // Store user input as well as KaTeX rendering.
        numberStored: [],
        algebraStored: [],

        parser: math.parser(),
        roundTo: 6,

        // For handling info-showing
        infoShown: false
    },

    // COMPUTED PROPERTIES
    computed: {
        inputPreview: function(){
            // If user input empty, return empty string.
            // Otherwise mathjs/nerdamer will try to process empty string and return "undefined"
            if (this[this.mode+'Input'] == '') {
                return '';
            }

            // Number preview
            if (this.mode=='number') {
                var os = '';
                try {
                    // NEED TO HANDLE LINE REFERENCES
                    var that = this;
                    os = this.numberInput.replace(/:\d+/g, function(x){
                        if (x==':') return '';
                        var i = parseInt(x.substr(1));
                        var v = that.numberStored[that.numberStored.length - i].val;
                        return (that.round(v, that.roundTo));
                    });

                    os = math.parse(os).toTex({parenthesis:'auto', implicit:'hide'});
                    os = os.replace(/:=/g,'=');

                    if (os.match(/end/)) throw "nope";
                } catch (err) {
                    os = '...';
                }
            }
            // Algebra preview
            else {
                var os = '';
                var inp = this.algebraInput;
                try {
                    // If variable/function declaration...
                    if (inp.indexOf("=") > -1){
                        // Need to split into two sides, decide if variable or function, handle functions accordingly
                        var [lhs, rhs] = inp.split("=");
                        // Function definition or variable definition?
                        if (/\(*\)/.test(lhs)) { // function defintion
                            var name = lhs.substring(0, lhs.indexOf("("));
                            var inpVars = lhs.substring(lhs.indexOf("(")+1, lhs.indexOf(")")).split(',');
                            os += (name.length > 1) ? ('\\mathrm{'+name+'}') : name;
                            os += '\\left(' + inpVars.join(',') + '\\right)' + "=";
                            os += nerdamer.convertToLaTeX(rhs);
                        } else { // Variable definition
                            os = nerdamer.convertToLaTeX(this.algebraInput);
                        }
                    } else {
                        os = nerdamer.convertToLaTeX(this.algebraInput);
                    }
                } catch (err) {
                    console.log(err);
                    os = '...';
                }
            }
            os = katex.renderToString(this.stripMathrm(os), {displayMode: true});
            return os;
        },
        outputs: function() {
            return this.mode=='number' ? this.numberStored : this.algebraStored;
        },

        appInfo: function(){
            var os = `
                
            `;
            if (this.mode === 'number') {
                os += `
                    <h1>What is this?</h1>
                    <p>This is a numerical calculator (built off of <a href="http://mathjs.org" target="_blank">MathJS</a>) for doing quick computations. The calculator will pretty-print your mathematics as you type it. For example, try typing "3/5 + cos(pi/2)" without the quotes, and then pressing Enter on your keyboard.</p>
                    <h1>Using previous output</h1>
                    <p>Once you have entered a computation, a number with a : in front of it will show up to the right of the computation (For example, :1 will show up next to your first computation). You can use this :# in later computations to reference previous values. For example, enter "pi/2", and then for the second computation enter "sin(:1)".</p>
                    <h1>Defining Variables/Functions</h1>
                    <p>You can define a variable/parameter by entering " = ". For example, you can enter "a = pi/4" and then reference a in later computations (such as "sin(a)"). Similarly, functions can be defined in a manner like "f(x) = cos(sin(x))" and then used in later computations like "(f(3)-f(1))/(3-1)".</p>
                `;
            } else {
                os += `
                    <h1>What is this?</h1>
                    <p>This is an algebra calculator (built off of <a href="http://nerdamer.com/" target="_blank">Nerdamer</a>) for doing algebraic computations. The calculator will pretty-print your mathematics as you type it. Once you press Enter on your keyboard, the calculator will try to run your computation.</p>

                    <h1>Defining Functions</h1>
                    <p>You can define a function by writing a function definition, such as "f(x) = cos(x^2)". You can use this function in later computations. For example, after defining f you can enter "diff(f(x))" to differentiate the function f.</p>

                    <h1>Numerical vs. Algebraic</h1>
                    <p>The pencil/calculator icon toggles whether computations are done symbolically or numerically. If the pencil is shown, computations will be handled algebraically -- If the calculator is shown, computations will be handled numerically. Press the calculator/pencil symbol to change modes. Also, pressing the esc key while in the input area will change the mode.</p>

                    <h1>Supported Functions</h1>
                    <p>Here is a brief list of supported functions.</p>
                    <ul>
                        <li>Trigonometric functions like: <code>cos</code>, <code>sin</code>, <code>tan</code>, <code>acos</code>, <code>asin</code>, <code>atan</code>, <code>sec</code>, <code>csc</code>, <code>cot</code>. For example, try entering <code>cos(pi/4)</code>.</li>
                        <li>Hyperbolic trig functions like: <code>cosh</code>, <code>sinh</code>, <code>tanh</code>. For example try entering <code>cosh(13)</code>.</li>
                        <li>The log function. For example, <code>log(100, 2)</code> will compute the log<sub>2</sub>(100). The <code>log10</code> function computes log base 10.</li>
                        <li><code>sqrt</code> computes the square root of a value. For example, <code>sqrt(4)</code> returns 2.</li>
                        <li><code>min</code> and <code>max</code> which will compute the minimum or maximum value of a list of numbers. For example, <code>min(3,5,7)</code> will return 3. (Make sure you are in numerical mode for this.)</li>
                        <li><code>floor</code> and <code>ceil</code> which are the floor and ceiling functions. <code>floor(3.2)</code> returns 3.</li>
                        <li><code>expand</code> takes an expression as an input, expands it and then prints the output. For example, <code>expand((x-1)^4)</code> will expand the expression (x-1)<sup>4</sup>.</li>
                        <li><code>sum(expression, variable, start, end)</code> computes a sum. For example, <code>sum(2*n+1, n, 0, 4)</code> computes the sum of the first 5 odd numbers.</li>
                        <li><code>product(expression, variable, start, end)</code> computes a product. For example, <code>product(2*n+1, n, 0, 4)</code> computes the product of the first 5 odd numbers.</li>
                        <li><code>diff(expression, variable, order)</code> computes the derivative of <code>expression</code> with respect to <code>variable</code>. Here are some examples: <code>diff(x^5)</code> will return 5*x^4. Notice that if only one argument is passed, the system will guess what you mean. <code>diff(x^2*y^2, y)</code> will return 2*y*x^2 because it is differentiating with respect to y. If you pass a third argument, it will compute higher-order derivatives [pass 2 as the third argument, and it will compute a second derivative].</li>
                        <li><code>integrate(expression, variable)</code> will compute the indefinite integral of <code>expression</code> with respect to <code>variable</code>. For example, <code>integrate(x^3, x)</code> will return x^4/4.</li>
                        <li><code>defint(expression, variable, lower bound, upper bound)</code> will compute a definite integral. For example, <code>defint(x^3, x, 1, pi)</code> will compute the integral of x^3 from 1 to pi. Enter the code into the input to see what the arguments are doing.</li>
                        <li><code>factor</code> will either factor a number into prime powers, or a polynomial into linear factors (if possible over the real numbers). For example, <code>factor(200)</code> will return the prime factorization of 200, and <code>factor(x^2-4)</code> will return (x-2)*(x+2).</li>
                    </ul>
                `;
            }
            return os;
        }
    },

    // METHODS OBJECT
    methods: {

        // When user enters a command.
        runCommand: function() {
            // If empty input, don't do anything
            if (this[this.mode+'Input'] == '') {
                console.log('empty');
                return false;
            }

            // Handle numeric case first
            if (this.mode == 'number') {
                try {
                    // NEED TO HANDLE LINE REFERENCES
                    var inp = this.numberInput.replace(/ /g, '');
                    var that = this;
                    inp = inp.replace(/:\d+/g, function(x){
                        if (x==':') return '';
                        var i = parseInt(x.substr(1));
                        var v = that.numberStored[that.numberStored.length - i].val;
                        return (that.round(v, that.roundTo));
                    });

                    // Check to see if variable declaration
                    if (inp.indexOf("=") > -1) {
                        this.parser.eval(inp);
                        var out = math.parse(inp).toTex({parenthesis:'auto', implicit:'hide'});
                        out = out.replace(/:=/g, '=');
                        out = katex.renderToString(this.stripMathrm(out), {displayMode: true});
                        this.numberStored.unshift({
                            inp: inp,
                            val: null,
                            def: true,
                            out: out
                        });
                    } else {
                        var val = this.parser.eval(inp);
                        if (inp === undefined || val == 'NaN') throw 'Nope';
                        var out = math.parse(inp).toTex({parenthesis:'auto', implicit:'hide'});
                        out = katex.renderToString(this.stripMathrm(out)+'='+this.round(val, this.roundTo), {displayMode: true});
                        this.numberStored.unshift({
                            inp: inp,
                            val: val,
                            def: false,
                            out: out
                        });
                        
                    }
                    // Push input to inputStored for reference later
                    this.numberInputStored.unshift(inp);
                    this.numberInput = '';
                } catch (err) {
                    console.log(err);
                    return false;
                }
            } 

            // Now handle algebra case
            else if (this.mode == 'algebra') {
                try {
                    var inp = this.algebraInput.replace(/ /g, '');
                    var out = '';
                    // Define a function or variable
                    if (inp.indexOf("=") > -1) {
                        var [lhs, rhs] = inp.split("=");
                        if (/\(*\)/.test(lhs)) { // function defintion
                            var name = lhs.substring(0, lhs.indexOf("("));
                            var inpVars = lhs.substring(lhs.indexOf("(")+1, lhs.indexOf(")")).split(',');
                            nerdamer.setFunction(name, inpVars, rhs);
                            out += (name.length > 1) ? ('\\mathrm{'+name+'}') : name;
                            out += '\\left(' + inpVars.join(',') + '\\right)' + "=";
                            out += nerdamer.convertToLaTeX(rhs);
                        } else { // Variable definition
                            nerdamer.setVar(lhs, rhs);
                            out += nerdamer.convertToLaTeX(inp);
                        }

                        
                        out = katex.renderToString(this.stripMathrm(out), {displayMode:true});
                        this.algebraStored.unshift({
                            inp: this.algebraInput,
                            def: true,
                            out: out
                        });
                    }
                    // No definition
                    else {
                        var out = nerdamer.convertToLaTeX(inp);
                        out += "=";
                        if (this.decimal) {
                            var rt = this.roundTo;
                            out += nerdamer(`round(10^${rt}*(${inp}))/(10^${rt})`, {}, ['numer']).evaluate();
                        } else {
                            out += nerdamer(inp, {}, []).toTeX();
                        }
                        out = katex.renderToString(this.stripMathrm(out), {displayMode:true});
                        this.algebraStored.unshift({
                            inp: this.algebraInput,
                            def: false,
                            out: out 
                        });
                    }

                    // Push input to inputStored for reference later
                    this.algebraInputStored.unshift(this.algebraInput);
                    this.algebraInput = '';
                } catch (err) {
                    console.log(err);
                    return false;
                }
            } 
            else {
                return false;
            }
            
        },

        deleteItem: function(i) {
            var toDelete = this[this.mode+'Stored'].splice(i, 1)[0];
            // If definition, need to clear element from parser
            if (toDelete.def) {
                // From Math
                if (this.mode=='number') {
                    // Need to get name of variable
                    var v = toDelete.inp.substring(0, toDelete.inp.indexOf('='));
                    v = v.replace(/\(\w+\)/g, '');
                    this.parser.remove(v);
                }
                // I don't think there's a way to clear a variable in nerdamer...
            }
        },

        // Clear all
        clearAll: function() {
            if (this.mode=='number') {
                this.parser.clear();
                this.numberStored = [];
                this.numberInput = '';
                this.$refs.numberInput.focus();
            } else {
                nerdamer.flush();
                nerdamer.clearVars();
                this.algebraStored = [];
                this.algebraInput = '';
                this.$refs.algebraInput.focus();
            }
        },

        // Move through stored inputs
        changeInput: function(mode, di) {
            var i = this[mode+'InputStoredIndex'] + parseInt(di);
            i = Math.min(i, this[mode+'InputStored'].length - 1);
            i = Math.max(i, -1);
            this[mode+'InputStoredIndex'] = i;
            if (di === 1) {
                if (i === 0){
                    this[mode+'InputTmp'] = this[mode+'Input'];
                }
                this[mode+'Input'] = this[mode+'InputStored'][i];
            } else {
                if (i === -1) {
                    this[mode+'Input'] = this[mode+'InputTmp'];
                } else {
                    this[mode+'Input'] = this[mode+'InputStored'][i];
                }
                
            }

        },

        // Method to handle rounding
        round: function(x, N) {
            return Math.round(x*Math.pow(10,N))/Math.pow(10,N)
        },

        // Remove \mathrm
        stripMathrm: function(inp) {
            var inp = inp.replace(/\\mathrm\{\w\}/g, function(x){
                var y = x.substring(x.length-2, x.length - 1);
                return y;
            });
            return inp;
        }

    }
});