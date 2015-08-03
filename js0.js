"use strict";

function generateSrc(src)
{
  var c = parse(src);
  var compiled = compile(c, "val", "next");
  return generate(compiled);
}

function generate(compiled)
{
  var generated0 = generate0(compiled.statements);
  var pre = "";
  var post = line("var __f = main; while(__f = __f());");
  return pre + generated0 + post;
}

function line(s)
{
  return s + "\n";
}

var instructionGenerator = {};
instructionGenerator.save =
  function (save)
  {
    return "stack.push(" + save.reg + ")";
  }
instructionGenerator.restore =
  function (restore)
  {
    return restore.reg + " = stack.pop()";
  }
instructionGenerator.assign =
  function (assign)
  {
    return assign.target + " = " + assign.x.visit(instructionGenerator);
  }
instructionGenerator.makeCompiledProcedure =
  function (makeCompiledProcedure)
  {
    return "[" + makeCompiledProcedure.label + ", env]";
  }
instructionGenerator.compiledProcedureEnv =
  function (compiledProcedureEnv)
  {
    return "proc[1]";
  }
instructionGenerator.compiledProcedureEntry =
  function (compiledProcedureEntry)
  {
    return "proc[0]";
  }
instructionGenerator.applyPrimitiveProcedure =
  function (applyPrimitiveProcedure)
  {
    return "proc(argl)";
  }
instructionGenerator.extendEnvironment =
  function (extendEnvironment)
  {
    var sb = "";
    sb += "env.extend(env, [";
    var formals = extendEnvironment.formals;
    if (formals !== Null)
    {
      sb += "\"" + formals.car + "\"";
      formals = formals.cdr;
      while (formals !== Null)
      {
        sb += ",\"" + formals.car + "\"";
        formals = formals.cdr;
      }
    }
    sb += "], argl)";
    return sb;
  }
instructionGenerator.lookupVariableValue =
  function (lookupVariableValue)
  {
    return "env.lookup(\"" + lookupVariableValue.exp + "\")";
  }
instructionGenerator.list =
  function (list)
  {
    return "new Pair(val, Null)";
  }
instructionGenerator.cons =
  function (cons)
  {
    return "new Pair(val,argl)";
  }
instructionGenerator.const =
  function (cnst)
  {
    var exp = cnst.exp;
    if (exp instanceof String)
    {
      return "\"" + exp + "\"";
    }
    if (exp === Null)
    {
      return "Null";
    }
    return String(exp);
  }
instructionGenerator.label =
  function (label)
  {
    return label.label;
  }
instructionGenerator.gotoLabel =
  function (gotoLabel)
  {
    return "return " + gotoLabel.label + "()";
  }
instructionGenerator.gotoReg =
  function (gotoReg)
  {
    return "return " + gotoReg.reg;
  }
instructionGenerator.testPrimitiveProcedure =
  function (primitiveProcedure)
  {
    return "flag = (typeof proc === \"function\")"; 
  }
instructionGenerator.testFalse =
  function (primitiveProcedure)
  {
    return "flag = !val"; 
  }
instructionGenerator.branch =
  function (branch)
  {
    return "if (flag) {return " + branch.label  + "()}";
  }
instructionGenerator.defineVariable =
  function (defineVariable)
  {
    return "env.add(\"" + defineVariable.exp + "\", val)";
  }
instructionGenerator.setVariableValue =
  function (setVariableValue)
  {
    return "env.set(\"" + setVariableValue.exp + "\", val)";
  }

function Env(parent)
{
  this.frame = new Map();
  this.parent = parent;
}

Env.prototype.add =
  function (name, value)
  {
    this.frame.set(name, value);
  }

Env.prototype.lookup =
  function (name)
  {
    var env = this;
    while (true)
    {
      if (env.frame.has(name))
      {
        return env.frame.get(name);
      }
      env = env.parent;
      if (!env)
      {
        throw new Error("variable not found: " + name);
      }      
    }
  }

Env.prototype.set =
  function (name, value)
  {
    var env = this;
    while (true)
    {
      if (env.frame.has(name))
      {
        env.frame.set(name, value);
        return;
      }
      env = env.parent;
      if (!env)
      {
        throw new Error("variable not found: " + name);
      }      
    }
  }

Env.prototype.extend =
  function(env, formals, argl)
  {
    var extended = new Env(env);
    formals.forEach(
      function (formal)
      {
        extended.add(formal, argl.car);
        argl = argl.cdr;
      })
    return extended;
  }

function generate0(seq)
{
  var generated = "";
  generated += line("function main() {");
  var previousInstruction = null;
  seq.forEach(
    function (instruction)
    {
      if (typeof instruction === "string")
      {
        if (!(previousInstruction instanceof GotoLabel || previousInstruction instanceof GotoReg))
        {
          generated += line("return " + instruction + "()");
        }
        generated += line("}");
        generated += line("function " + instruction + "() {");
      }
      else
      {
        generated += line(instruction.visit(instructionGenerator));
      }
      previousInstruction = instruction;
    });
  generated += line("}");
  return generated;
}

var globalEnv = new Env();
globalEnv.add("+",
  function(argl)
  {
    var result = 0;
    while (argl !== Null)
    {
      result += argl.car;
      argl = argl.cdr;
    }
    return result;
  })
globalEnv.add("-",
  function(argl)
  {
    var result = argl.car;
    if (argl.cdr === Null)
    {
      return -result;
    }
    argl = argl.cdr;
    while (argl !== Null)
    {
      result -= argl.car;
      argl = argl.cdr;
    }
    return result;
  })
globalEnv.add("*",
  function(argl)
  {
    var result = 1;
    while (argl !== Null)
    {
      result *= argl.car;
      argl = argl.cdr;
    }
    return result;
  })
globalEnv.add("/",
  function(argl)
  {
    var result = argl.car;
    if (argl.cdr === Null)
    {
      return 1/result;
    }
    argl = argl.cdr;
    while (argl !== Null)
    {
      result /= argl.car;
      argl = argl.cdr;
    }
    return result;
  })
globalEnv.add("<",
  function(argl)
  {
    return argl.car < argl.cdr.car;
  })
globalEnv.add("<=",
  function(argl)
  {
    return argl.car <= argl.cdr.car;
  })
globalEnv.add(">=",
  function(argl)
  {
    return argl.car >= argl.cdr.car;
  })
