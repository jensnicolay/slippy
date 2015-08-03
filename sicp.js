"use strict";

function compileSrc(src)
{
  var c = parse(src);
  var compiled = compile(c, "val", "next");
  return compiled.needs + "\n" + compiled.modifies + "\n" + compiled.statements.join("\n");
}

function parse(src)
{
  return new SchemeParser().parse(src)[0];
}

var __labelCounter__ = 0;

function makeLabel(l)
{
  return l + (__labelCounter__++);
}

function compile(exp, target, linkage)
{  
  if (exp instanceof Number || exp instanceof Boolean || exp instanceof String)
  {
    return compileLiteral(exp, target, linkage)
  }
  else if (exp instanceof Sym)
  {
    return compileVariable(exp, target, linkage)
  }
  else if (exp instanceof Pair)
  {
    var car = exp.car;
    if (car instanceof Sym)
    {
      var name = car.name;
      if (name === "lambda")
      {
        return compileLambda(exp, target, linkage); 
      }
      else if (name === "define")
      {
        return compileDefinition(exp, target, linkage);
      }
      else if (name === "if")
      {
        return compileIf(exp, target, linkage);
      }
      else if (name === "begin")
      {
        return compileSequence(exp.cdr, target, linkage);
      }
      else if (name === "set!")
      {
        return compileAssignment(exp, target, linkage);
      }
      else
      {
        return compileApplication(exp, target, linkage);
      }
    }
  }
  else
  {
    throw new Error("cannot handle: " + exp);
  }
}

function makeInstructionSequence(needs, modifies, statements)
{
  assert(Array.isArray(statements));
  return {needs:needs, modifies:modifies, statements:statements};
}

function emptyInstructionSequence()
{
  return makeInstructionSequence([], [], []);
}

function compileLinkage(linkage)
{
  if (linkage === "return")
  {
    return makeInstructionSequence(["kontinue"], [], [new GotoReg("kontinue")]); 
  }
  if (linkage === "next")
  {
    return emptyInstructionSequence();
  }
  return makeInstructionSequence([], [], [new GotoLabel(linkage)]);
}

function endWithLinkage(linkage, instructionSequence)
{
  return preserving(["kontinue"],
      instructionSequence,
      compileLinkage(linkage));
}

function compileLiteral(exp, target, linkage)
{
  return endWithLinkage(linkage, 
      makeInstructionSequence([], [target],
          [new Assign(target, new Const(exp))]));
}

function compileVariable(exp, target, linkage)
{
  return endWithLinkage(linkage,
      makeInstructionSequence(["env"], [target],
          [new Assign(target, new LookupVariableValue(exp))]));
}

function compileAssignment(exp, target, linkage)
{
  var v = exp.cdr.car;
  var getValueCode = compile(exp.cdr.cdr.car, "val", "next");
  return endWithLinkage(linkage,
      preserving(["env"],
          getValueCode,
          makeInstructionSequence(["env", "val"], [target],
              [new SetVariableValue(v), new Assign(target, new Const(new String("ok")))])));
}

function compileDefinition(exp, target, linkage)
{
  var v = exp.cdr.car;
  var getValueCode = compile(exp.cdr.cdr.car, "val", "next");
  return endWithLinkage(linkage,
      preserving(["env"],
          getValueCode,
          makeInstructionSequence(["env", "val"], [target],
              [new DefineVariable(v), new Assign(target, new Const(new String("ok")))])));
}

function compileIf(exp, target, linkage)
{
  var tbranch = makeLabel("trueBranch");
  var fbranch = makeLabel("falseBranch");
  var afterIf = makeLabel("afterIf");
  var consequentLinkage = (linkage === "next" ? afterIf : linkage);
  var pcode = compile(exp.cdr.car, "val", "next");
  var ccode = compile(exp.cdr.cdr.car, target, consequentLinkage);
  var acode = compile(exp.cdr.cdr.cdr.car, target, linkage);
  return preserving(["env", "kontinue"],
      pcode,
      append3Sequences(
          makeInstructionSequence(["val"], [], [new TestFalse(), new Branch(fbranch)]),
          parallelInstructionSequences(
              append2Sequences(tbranch, ccode),
              append2Sequences(fbranch, acode)),
          afterIf));
}

function compileSequence(seq, target, linkage)
{
  if (seq.cdr === Null)
  {
    return compile(seq.car, target, linkage);
  }
  return preserving(["env", "kontinue"],
      compile(seq.car, target, "next"),
      compileSequence(seq.cdr, target, linkage));
}

function compileLambda(exp, target, linkage)
{
  var procEntry = makeLabel("entry");
  var afterLambda = makeLabel("afterLambda");
  var lambdaLinkage = linkage === "next" ? afterLambda : linkage;
  return append2Sequences(
      tackOnInstructionSequence(
          endWithLinkage(
              lambdaLinkage,
              makeInstructionSequence(["env"], [target], [new Assign(target, new MakeCompiledProcedure(procEntry))])),
          compileLambdaBody(exp, procEntry)),
      afterLambda);
}

function compileLambdaBody(exp, procEntry)
{
  var formals = exp.cdr.car;
  return append2Sequences(
      makeInstructionSequence(["env","proc","argl"], ["env"],
          [procEntry, new Assign("env", new CompiledProcedureEnv()), new Assign("env", new ExtendEnvironment(formals))]),
      compileSequence(exp.cdr.cdr, "val", "return"));
}

function compileApplication(exp, target, linkage)
{
  var procCode = compile(exp.car, "proc", "next");
  var operands = exp.cdr;
  var operandCodes = [];
  while (operands !== Null)
  {
    var operand = operands.car;
    operandCodes.push(compile(operand, "val", "next"));
    operands = operands.cdr;
  }
  return preserving(["env", "kontinue"],
      procCode,
      preserving(["proc", "kontinue"],
          constructArgList(operandCodes),
          compileProcedureCall(target, linkage)));
}

function constructArgList(operandCodes)
{
  operandCodes = operandCodes.reverse();
  if (operandCodes.length === 0)
  {
    return makeInstructionSequence([],["argl"],
        [new Assign("argl", new Const(Null))]);
  }
  var codeToGetLastArg =
    append2Sequences(
        operandCodes[0],
        makeInstructionSequence(["val"], ["argl"],
          [new Assign("argl", new List())]));
  if (operandCodes.length === 1)
  {
    return codeToGetLastArg;
  }
  return preserving(["env"],
      codeToGetLastArg, 
      codeToGetRestArgs(operandCodes.slice(1)));
}

function codeToGetRestArgs(operandCodes)
{
  var codeForNextArg = 
    preserving(["argl"],
        operandCodes[0],
        makeInstructionSequence(["val", "argl"], ["argl"],
            [new Assign("argl", new Cons())]));
  if (operandCodes.length === 1)
  {
    return codeForNextArg;
  }
  return preserving(["env"],
      codeForNextArg,
      codeToGetRestArgs(operandCodes.slice(1)));
}

function compileProcedureCall(target, linkage)
{
  var primitiveBranch = makeLabel("primitiveBranch");
  var compiledBranch = makeLabel("compiledBranch");
  var afterCall = makeLabel("afterCall");
  var compiledLinkage = (linkage === "next" ? afterCall : linkage);
  return append3Sequences(
      makeInstructionSequence(["proc"], [], [new TestPrimitiveProcedure(), new Branch(primitiveBranch)]),
      parallelInstructionSequences(
          append2Sequences(
              compiledBranch,
              compileProcAppl(target, compiledLinkage)),
          append2Sequences(
              primitiveBranch,
              endWithLinkage(linkage, makeInstructionSequence(["proc", "argl"], [target], [new Assign(target, new ApplyPrimitiveProcedure())])))),
      afterCall);
}

var allRegs = ["env", "proc", "val", "argl", "kontinue"];

function compileProcAppl(target, linkage)
{
  if (target === "val" && linkage !== "return")
  {
    return makeInstructionSequence(["proc"], allRegs,
        [new Assign("kontinue", new Label(linkage)),
         new Assign("val", new CompiledProcedureEntry()),
         new GotoReg("val")]);
  }
  if (target !== "val" && linkage !== "return")
  {
    var procReturn = makeLabel("procReturn");
    return makeInstructionSequence(["proc"], allRegs,
        [new Assign("kontinue", new Label(procReturn)),
         new Assign("val", new CompiledProcedureEntry()),
         new GotoReg("val"),
         procReturn,
         new Assign(target, new Reg("val")),
         new GotoLabel(linkage)]);
  }
  if (target === "val" && linkage === "return")
  {
    return makeInstructionSequence(["proc", "kontinue"], allRegs,
        [new Assign("val", new CompiledProcedureEntry()),
         new GotoReg("val")]);
  }
  if (target !== "val" && linkage === "return")
  {
    throw new Error("return linkage, target not val: " + target);
  }
}

function registersNeeded(s)
{
  if (typeof s === "string")
  {
    return [];
  }
  return s.needs;
}

function registersModified(s)
{
  if (typeof s === "string")
  {
    return [];
  }
  return s.modifies;
}

function statements(s)
{
  if (typeof s === "string")
  {
    return [s];
  }
  return s.statements;
}

function contains(x, s)
{
  return s.indexOf(x) > -1;
}

function needsRegister(seq, reg)
{
  return contains(reg, registersNeeded(seq));
}

function modifiesRegister(seq, reg)
{
  return contains(reg, registersModified(seq));
}

function append2Sequences(seq1, seq2)
{
  return makeInstructionSequence(
      listUnion(registersNeeded(seq1),
          listDifference(registersNeeded(seq2),
              registersModified(seq1))),
              listUnion(registersModified(seq1),
                  registersModified(seq2)),
                  statements(seq1).concat(statements(seq2)));
}

function append3Sequences(seq1, seq2, seq3)
{
  return append2Sequences(seq1, append2Sequences(seq2, seq3));
}

function listUnion(s1, s2)
{
  if (s1.length === 0)
  {
    return s2;
  }
  if (contains(s1[0], s2))
  {
    return listUnion(s1.slice(1), s2);
  }
  return [s1[0]].concat(listUnion(s1.slice(1), s2));
}

function listDifference(s1, s2)
{
  if (s1.length === 0)
  {
    return [];
  }
  if (contains(s1[0], s2))
  {
    return listDifference(s1.slice(1), s2);
  }
  return [s1[0]].concat(listDifference(s1.slice(1), s2));
}

function preserving(regs, seq1, seq2)
{
  if (regs.length === 0)
  {
    return append2Sequences(seq1, seq2);
  }
  var firstReg = regs[0];
  if (needsRegister(seq2, firstReg) && modifiesRegister(seq1, firstReg))
  {
    return preserving(regs.slice(1),
        makeInstructionSequence(
          listUnion([firstReg], registersNeeded(seq1)),
          listDifference(registersModified(seq1), [firstReg]),
          [new Save(firstReg)].concat(statements(seq1).concat([new Restore(firstReg)]))),
        seq2);
  }
  return preserving(regs.slice(1), seq1, seq2);
}

function tackOnInstructionSequence(seq, bodySeq)
{
  return makeInstructionSequence(registersNeeded(seq), registersModified(seq), statements(seq).concat(statements(bodySeq)));
}

function parallelInstructionSequences(seq1, seq2)
{
  return makeInstructionSequence(
      listUnion(registersNeeded(seq1), registersNeeded(seq2)),
      listUnion(registersModified(seq1), registersModified(seq2)),
      statements(seq1).concat(statements(seq2)));
}

/****/

function Const(exp)
{
  this.exp = exp
}

Const.prototype.toString =
  function ()
  {
    return "(const " + this.exp + ")";
  }

Const.prototype.visit =
  function (v)
  {
    return v.const(this);
  }

function Reg(reg)
{
  this.reg = reg
}

Reg.prototype.toString =
  function ()
  {
    return "(reg " + this.reg + ")";
  }

Reg.prototype.visit =
  function (v)
  {
    return v.reg(this);
  }

function Save(reg)
{
  this.reg = reg
}

Save.prototype.toString =
  function ()
  {
    return "(save " + this.reg + ")";
  }

Save.prototype.visit =
  function (v)
  {
    return v.save(this);
  }

function Restore(reg)
{
  this.reg = reg
}

Restore.prototype.toString =
  function ()
  {
    return "(restore " + this.reg + ")";
  }

Restore.prototype.visit =
  function (v)
  {
    return v.restore(this);
  }

function Label(label)
{
  this.label = label
}

Label.prototype.toString =
  function ()
  {
    return "(label " + this.label + ")";
  }

Label.prototype.visit =
  function (v)
  {
    return v.label(this);
  }

function LookupVariableValue(exp)
{
  this.exp = exp;
}

LookupVariableValue.prototype.toString =
  function ()
  {
    return "(lookup-variable-value " + this.exp + ")";
  }

LookupVariableValue.prototype.visit =
  function (v)
  {
    return v.lookupVariableValue(this);
  }

function DefineVariable(exp)
{
  this.exp = exp;
}

DefineVariable.prototype.toString =
  function ()
  {
    return "(define-variable! " + this.exp + ")";
  }

DefineVariable.prototype.visit =
  function (v)
  {
    return v.defineVariable(this);
  }

function SetVariableValue(exp)
{
  this.exp = exp;
}

SetVariableValue.prototype.toString =
  function ()
  {
    return "(set-variable-value! " + this.exp + ")";
  }

SetVariableValue.prototype.visit =
  function (v)
  {
    return v.setVariableValue(this);
  }

function Assign(target, x)
{
  this.target = target;
  this.x = x;
}

Assign.prototype.toString =
  function ()
  {
    return "(assign " + this.target + " " + this.x + ")";
  }

Assign.prototype.visit =
  function (v)
  {
    return v.assign(this);
  }

function GotoReg(reg)
{
  this.reg = reg;
}

GotoReg.prototype.toString =
  function ()
  {
    return "(goto-reg " + this.reg + ")";
  }

GotoReg.prototype.visit =
  function (v)
  {
    return v.gotoReg(this);
  }

function GotoLabel(label)
{
  this.label = label;
}

GotoLabel.prototype.toString =
  function ()
  {
    return "(goto-label " + this.label + ")";
  }

GotoLabel.prototype.visit =
  function (v)
  {
    return v.gotoLabel(this);
  }

function TestFalse()
{
}

TestFalse.prototype.toString =
  function ()
  {
    return "(test-false)";
  }

TestFalse.prototype.visit =
  function (v)
  {
    return v.testFalse(this);
  }

function TestPrimitiveProcedure()
{
}

TestPrimitiveProcedure.prototype.toString =
  function ()
  {
    return "(test-primitive-procedure)";
  }

TestPrimitiveProcedure.prototype.visit =
  function (v)
  {
    return v.testPrimitiveProcedure(this);
  }

function Branch(label)
{
  this.label = label;
}

Branch.prototype.toString =
  function ()
  {
    return "(branch " + this.label + ")";
  }

Branch.prototype.visit =
  function (v)
  {
    return v.branch(this);
  }

function List()
{
}

List.prototype.toString =
  function ()
  {
    return "(list)";  
  }

List.prototype.visit =
  function (v)
  {
    return v.list(this);
  }

function Cons()
{
}

Cons.prototype.toString =
  function ()
  {
    return "(cons)";  
  }

Cons.prototype.visit =
  function (v)
  {
    return v.cons(this);
  }

function CompiledProcedureEntry()
{
}

CompiledProcedureEntry.prototype.toString =
  function ()
  {
    return "(compiled-procedure-entry)";  
  }

CompiledProcedureEntry.prototype.visit =
  function (v)
  {
    return v.compiledProcedureEntry(this);
  }

function ExtendEnvironment(formals)
{
  this.formals = formals;
}

ExtendEnvironment.prototype.toString =
  function ()
  {
    return "(extend-environment " + this.formals + ")";
  }

ExtendEnvironment.prototype.visit =
  function (v)
  {
    return v.extendEnvironment(this);
  }

function MakeCompiledProcedure(label)
{
  this.label = label;
}

MakeCompiledProcedure.prototype.toString =
  function ()
  {
    return "(make-compiled-procedure " + this.label + ")";  
  }

MakeCompiledProcedure.prototype.visit =
  function (v)
  {
    return v.makeCompiledProcedure(this);
  }

function ApplyPrimitiveProcedure()
{
}

ApplyPrimitiveProcedure.prototype.toString =
  function ()
  {
    return "(apply-primitive-procedure)";  
  }

ApplyPrimitiveProcedure.prototype.visit =
  function (v)
  {
    return v.applyPrimitiveProcedure(this);
  }


function CompiledProcedureEnv()
{
}

CompiledProcedureEnv.prototype.toString =
  function ()
  {
    return "(compiled-procedure-env)";  
  }

CompiledProcedureEnv.prototype.visit =
  function (v)
  {
    return v.compiledProcedureEnv(this);
  }