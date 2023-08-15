theory Chapter3
  imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

section "Chapter 3.1"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n"
| "aval (V x) s = s x"
| "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n"
| "asimp_const (V x) = V x"
| "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of
      (N n1, N n2) \<Rightarrow> N (n1 + n2)
    | (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)"
| "plus (N i) a = (if i=0 then a else Plus (N i) a)"
| "plus a (N i) = (if i=0 then a else Plus a (N i))"
| "plus a1 a2 = Plus a1 a2"

lemma eval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction a1 a2 rule: plus.induct)
  apply (auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n"
| "asimp (V x) = V x"
| "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto simp add: eval_plus)
  done

(* Exercises *)

(* 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (Plus (N i1) (N i2)) = False"
| "optimal _ = True"

lemma "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done

(* 3.2 *)

(* 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (N n) = N n"
| "subst x a (V y) = (if x = y then a else V y)"
| "subst x a (Plus e1 e2) = Plus (subst x a e1) (subst x a e2)"

lemma substitution: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
    apply (auto)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction e)
    apply (auto)
  done

(* 3.4 *)
datatype aexpm = Nm int | Vm vname | Plusm aexpm aexpm | Timesm aexpm aexpm

fun amval :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
  "amval (Nm n) s = n"
| "amval (Vm x) s = s x"
| "amval (Plusm e1 e2) s = amval e1 s + amval e2 s"
| "amval (Timesm e1 e2) s = amval e1 s * amval e2 s"

fun mplus :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
  "mplus (Nm i1) (Nm i2) = Nm (i1 + i2)"
| "mplus (Nm i) a = (if i=0 then a else Plusm (Nm i) a)"
| "mplus a (Nm i) = (if i=0 then a else Plusm a (Nm i))"
| "mplus a1 a2 = Plusm a1 a2"

fun mtimes :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
  "mtimes (Nm i1) (Nm i2) = Nm (i1 * i2)"
| "mtimes (Nm i) e = (if i = 0 then Nm 0 else (if i = 1 then e else Timesm (Nm i) e))"
| "mtimes e (Nm i) = (if i = 0 then Nm 0 else (if i = 1 then e else Timesm (Nm i) e))"
| "mtimes e1 e2 = Timesm e1 e2"

lemma amval_plus: "amval (mplus a1 a2) s = amval a1 s + amval a2 s"
  apply (induction a1 a2 rule: mplus.induct)
  apply (auto)
  done

lemma amval_times: "amval (mtimes e1 e2) s = amval e1 s * amval e2 s"
  apply (induction e1 e2 rule: mtimes.induct)
  apply (auto )
  done

fun amsimp :: "aexpm \<Rightarrow> aexpm" where
  "amsimp (Nm n) = Nm n"
| "amsimp (Vm x) = Vm x"
| "amsimp (Plusm a1 a2) = mplus (amsimp a1) (amsimp a2)"
| "amsimp (Timesm e1 e2) = mtimes (amsimp e1) (amsimp e2)"

lemma "amval (amsimp a) s = amval a s"
  apply (induction a)
  apply (auto simp add: amval_plus amval_times)
  done

(* 3.5 *)
datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Times2 aexp2 aexp2 | Div2 aexp2 aexp2 | PInc2 vname

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 i) s = Some (i, s)"
| "aval2 (V2 x) s = Some (s x, s)"
| "aval2 (Plus2 e1 e2) s = (case aval2 e1 s of
      None \<Rightarrow> None
    | Some (i1, s') \<Rightarrow> (case aval2 e2 s' of
        None \<Rightarrow> None
      | Some (i2, s'') \<Rightarrow> Some (i1 + i2, s'')))"
| "aval2 (Times2 e1 e2) s = (case aval2 e1 s of
      None \<Rightarrow> None
    | Some (i1, s') \<Rightarrow> (case aval2 e2 s' of
        None \<Rightarrow> None
      | Some (i2, s'') \<Rightarrow> Some (i1 * i2, s'')))"
| "aval2 (Div2 e1 e2) s = (case aval2 e1 s of
      None \<Rightarrow> None
    | Some (i1, s') \<Rightarrow> (case aval2 e2 s' of
        None \<Rightarrow> None
      | Some (i2, s'') \<Rightarrow> (if i2 = 0 then None else Some (i1 div i2, s''))))"
| "aval2 (PInc2 x) s = Some (s x, s(x := s x + 1))"

(* 3.6 *)
datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl i) s = i"
| "lval (Vl x) s = s x"
| "lval (Plusl e1 e2) s = lval e1 s + lval e2 s"
| "lval (LET x e1 e2) s = lval e2 (s(x := lval e1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl i) = N i"
| "inline (Vl x) = V x"
| "inline (Plusl e1 e2) = Plus (inline e1) (inline e2)"
| "inline (LET x e1 e2) = subst x (inline e1) (inline e2)"

lemma "aval (inline e) s = lval e s"
  apply (induction e arbitrary: s)
    apply (auto simp add: substitution)
  done


section "Chapter 3.2"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v"
| "bval (Not b) s = (\<not> bval b s)"
| "bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"
| "bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

(* Exercises *)

(* 3.7 *)
fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"
fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a1 a2 = Not (Less a2 a1)"

lemma "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply (auto)
  done

lemma "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply (auto)
  done

(* 3.8 *)
datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 v) s = v"
| "ifval (If c i1 i2) s = (if ifval c s then ifval i1 s else ifval i2 s)"
| "ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v"
| "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)"
| "b2ifexp (And b1 b2) = If (b2ifexp b1) (b2ifexp b2) (Bc2 False)"
| "b2ifexp (Less a1 a2) = Less2 a1 a2"

lemma "ifval (b2ifexp b) s = bval b s"
  apply (induction b)
    apply (auto)
  done

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = Bc v"
| "if2bexp (If c i1 i2) = Not (And (Not (And (if2bexp c) (if2bexp i1))) (Not (And (Not (if2bexp c)) (if2bexp i2))))"
| "if2bexp (Less2 a1 a2) = Less a1 a2"

lemma "bval (if2bexp i) s = ifval i s"
  apply (induction i)
    apply (auto)
  done

(* 3.9 *)
datatype pbexp = VAR vname | NEG pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR x) s = s x"
| "pbval (NEG b) s = (\<not> pbval b s)"
| "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)"
| "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR x) = True"
| "is_nnf (NEG (VAR x)) = True"
| "is_nnf (NEG _) = False"
| "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)"
| "is_nnf (OR b1 b2) = (is_nnf b1 \<and> is_nnf b2)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (NEG (NEG b)) = nnf b"
| "nnf (NEG (AND b1 b2)) = OR (nnf (NEG b1)) (nnf (NEG b2))"
| "nnf (NEG (OR b1 b2)) = AND (nnf (NEG b1)) (nnf (NEG b2))"
| "nnf (AND b1 b2) = AND (nnf b1) (nnf b2)"
| "nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"
| "nnf b = b"

lemma "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct)
    apply (auto)
  done

lemma "is_nnf (nnf b)"
  apply (induction b rule: nnf.induct)
  apply (auto)
  done

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (AND (OR _ _) _) = False"
| "is_dnf (AND _ (OR _ _)) = False"
| "is_dnf (AND b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
| "is_dnf (OR b1 b2) = (is_dnf b1 \<and> is_dnf b2)"
| "is_dnf b = is_nnf b"

fun dist_and :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dist_and (OR b1 b2) b3 = OR (dist_and b1 b3) (dist_and b2 b3)"
| "dist_and b1 (OR b2 b3) = OR (dist_and b1 b2) (dist_and b1 b3)"
| "dist_and b1 b2 = AND b1 b2"

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = VAR x"
| "dnf_of_nnf (NEG b) = NEG b" (* Fine, because it only has to work for nnf inputs *)
| "dnf_of_nnf (AND b1 b2) = dist_and (dnf_of_nnf b1) (dnf_of_nnf b2)"
| "dnf_of_nnf (OR b1 b2) = OR (dnf_of_nnf b1) (dnf_of_nnf b2)"

lemma dist_and_correct: "pbval (dist_and b1 b2) s = pbval (AND b1 b2) s"
  apply (induction b1 b2 rule: dist_and.induct)
    apply (auto)
  done

lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply (induction b rule: dnf_of_nnf.induct)
    apply (auto split: pbexp.split simp add: dist_and_correct)
  done

lemma dist_and_dnf: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_and b1 b2)"
  apply (induction b1 b2 rule: dist_and.induct)
    apply (auto)
  done

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply (induction b rule: dnf_of_nnf.induct)
    apply (auto split: pbexp.split simp add: dist_and_dnf)
  done


section \<open>Chapter 3.3\<close>

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

(* Exercises *)

(* 3.10 *)
fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec1 (LOADI n) _ stk = Some (n # stk)"
| "exec1 (LOAD x) s stk = Some (s x # stk)"
| "exec1 ADD _ (j # i # stk) = Some ((i + j) # stk)"
| "exec1 ADD _ _ = None"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
  "exec [] _ stk = Some stk"
| "exec (i#is) s stk = (case exec1 i s stk of None \<Rightarrow> None | Some stk' \<Rightarrow> exec is s stk')"

fun comp :: "aexp \<Rightarrow> instr list" where
  "comp (N n) = [LOADI n]"
| "comp (V x) = [LOAD x]"
| "comp (Plus e1 e2) = comp e1 @ comp e2 @ [ADD]"

lemma exec_seq: "exec (is1 @ is2) s stk = (case exec is1 s stk of None \<Rightarrow> None
                                                                  | Some stk' \<Rightarrow> exec is2 s stk')"
  apply (induction is1 arbitrary: stk)
    apply (auto split: option.splits)
  done

lemma "exec (comp a) s stk = Some (aval a s # stk)"
  apply (induction a arbitrary: stk)
    apply (auto simp add: exec_seq)
  done

(* 3.11 *)
type_synonym reg = nat
datatype rinstr = LDI int reg | LD vname reg | ADD reg reg

fun rexec1 :: "rinstr \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "rexec1 (LDI n r)  _ regs = regs(r := n)"
| "rexec1 (LD x r) s regs = regs(r := s x)"
| "rexec1 (ADD r1 r2) _ regs = regs(r1 := regs r1 + regs r2)"

fun rexec :: "rinstr list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "rexec [] _ regs = regs"
| "rexec (i#is) s regs = rexec is s (rexec1 i s regs)"

fun rcomp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr list" where
  "rcomp (N n) r = [LDI n r]"
| "rcomp (V x) r = [LD x r]"
| "rcomp (Plus a1 a2) r = rcomp a1 r @ rcomp a2 (r+1) @ [ADD r (r+1)]"

lemma rexec_seq: "rexec (is1 @ is2) s regs = rexec is2 s (rexec is1 s regs)"
  apply (induction is1 arbitrary: regs)
    apply (auto)
  done

lemma rcomp_unmodified: "r1 < r2 \<Longrightarrow> (rexec (rcomp a r2) s regs) r1 = regs r1"
  apply (induction a arbitrary: r1 r2 regs)
    apply (auto simp add: rexec_seq)
  done

lemma "rexec (rcomp a r) s regs r = aval a s"
  apply (induction a arbitrary: r regs)
    apply (auto simp add: rexec_seq rcomp_unmodified)
  done

(* 3.12 *)
datatype rinstr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun r0exec1 :: "rinstr0 \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "r0exec1 (LDI0 n)  _ regs = regs(0 := n)"
| "r0exec1 (LD0 x) s regs = regs(0 := s x)"
| "r0exec1 (MV0 r) _ regs = regs(r := regs 0)"
| "r0exec1 (ADD0 r) _ regs = regs(0 := regs 0 + regs r)"

fun r0exec :: "rinstr0 list \<Rightarrow> state \<Rightarrow> (reg \<Rightarrow> int) \<Rightarrow> reg \<Rightarrow> int" where
  "r0exec [] _ regs = regs"
| "r0exec (i#is) s regs = r0exec is s (r0exec1 i s regs)"

fun r0comp :: "aexp \<Rightarrow> reg \<Rightarrow> rinstr0 list" where
  "r0comp (N n) _ = [LDI0 n]"
| "r0comp (V x) _ = [LD0 x]"
| "r0comp (Plus a1 a2) r = r0comp a1 r @ [MV0 (r+1)] @ r0comp a2 (r+1) @ [ADD0 (r+1)]"

lemma r0exec_seq: "r0exec (is1 @ is2) s regs = r0exec is2 s (r0exec is1 s regs)"
  apply (induction is1 arbitrary: regs)
    apply (auto)
  done

lemma r0comp_unmodified: "r1 \<noteq> 0 \<Longrightarrow> r1 \<le> r2 \<Longrightarrow> (r0exec (r0comp a r2) s regs) r1 = regs r1"
  apply (induction a arbitrary: r1 r2 regs)
    apply (auto simp add: r0exec_seq)
  done

lemma "r0exec (r0comp a r) s regs 0 = aval a s"
  apply (induction a arbitrary: r regs)
    apply (auto simp add: r0exec_seq r0comp_unmodified)
  done

end