theory Chapter7
  imports Main
    "~~/src/HOL/IMP/Com"
    "~~/src/HOL/IMP/Big_Step"
    "~~/src/HOL/IMP/Small_Step"
begin

value "''x'' ::= Plus (V ''y'') (N 1);; ''y'' ::= N 2"

(* Ex 7.1 *)
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned SKIP = {}"
| "assigned (Assign x _) = {x}"
| "assigned (Seq c1 c2) = assigned c1 \<union> assigned c2"
| "assigned (If b c1 c2) = assigned c1 \<union> assigned c2"
| "assigned (While b c) = assigned c"

lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
proof (induction rule: big_step_induct)
qed auto



end