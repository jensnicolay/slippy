function repl()
{
  var src = "\"Slippy compiler 0.1\"";
  var env = globalEnv;
  var stack = [];
  var val,flag,proc,argl,kontinue;
  
  while (src !== "(exit)")
  {
    var generated = generateSrc(src);
    var start = performance.now();
    eval(generated);
    var duration = performance.now() - start;
    print("time", duration);
    print(val);
    write(">>>");
    src = readline();
  }
  print("Slippy terminated");
}

function ev(src)
{
  var generated = generateSrc(src);
  var f = new Function("env", "stack", "val", "proc", "argl", "kontinue", "flag", generated + "return val");
  var start = performance.now();
  var result = f(globalEnv, []);
  var duration = performance.now() - start;
  print("time", duration);
  return result;
}

var square = "(begin (define sq (lambda (x) (* x x))) (sq 4))";
var factorial = "(define factorial (lambda (n) (if (= n 1) 1 (* (factorial (- n 1)) n))))"; 
var fib = "(begin (define fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))) (fib 33))";