pluscal options
---- MODULE name_of_file ----
(* import statements *)
EXTENDS <MODULE1>, <M2>, ...

(* 
  Constants are values that are dependent on the particular model. 
  All constants must be specified for the model to run.
*)
CONSTANTS <C1>, <C2>, ... \* CONSTANT also works
ASSUME <Expression1> \* Optional. If Expression is false, model cannot run.
ASSUME <Expression2> \* ASSUME expression can only depend on constants

RECURSIVE <rOp1(_)> \* recursive operators must be declared in advance

Op == <Expression>
Op(a, b, c) == <Exp>
Op(op2(_), a) == <Exp> \* Syntax to use a higher-order operator

(* --algorithm <algorithm>
\* variables global to algorithm
variables v1   = <Value>, 
          v2 \in <Set1>, \* v2 can be any element in the set
          v3 \in <Set2>; \* All <<v2, v3>> possibilities will be tested

\* Any operators in a define block can reference PlusCal variables
define
  Op == <Exp>
end define;

macro Macro(<var1>, <var2> ...) 
begin
    <UnlabeledPlusCal>
end macro;

procedure Procedure(<var1>, <var2>)
variables proc_v1 = <Exp>, ... \* no \in
begin
  <LabeledPlusCal>
  return;
end procedure;

(* 
   Each process has a value. All values must be comparable
   Inside a process you can retrieve its value with `self`
*)
process Single_Process = <Exp>
variables v1 = <Exp>, v2 \in <Set>; \* local to process
begin
    <LabeledPlusCal>
end process;

process Process \in <Set> \* one process per element
variables v1 \in <Set>; \* similar processes can choose different elements
begin
    <LabeledPlusCal>
end process;

(* For a single process system, instead of processes you do
   <Variables>
   <Define>
   <Macros>
   <Procedures>
   begin
     <PlusCal>
   end algorithm; *)

end algorithm; *)

====

