theory Chapter4
  imports Main
begin

section \<open>Chapter 4.2\<close>

(* Exercise 4.1 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}"
| "set (Node l a r) = set l \<union> {a} \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True"
| "ord (Node l a r) = (ord l \<and> ord r \<and> (\<forall> x \<in> set l. x < a) \<and> (\<forall> x \<in> set r. x > a))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins x Tip = Node Tip x Tip"
| "ins x (Node l a r) = (if x < a then Node (ins x l) a r else
    (if x > a then Node l a (ins x r) else Node l a r))"

lemma ins_inserts: "set (ins x t) = {x} \<union> set t"
  apply (induction t)
    apply (auto)
  done

lemma "ord t \<Longrightarrow> ord (ins x t)"
  apply (induction t)
    apply (auto simp add: ins_inserts)
  done

chapter \<open>Chapter 4.5\<close>

inductive ev :: "nat \<Rightarrow> bool" where
  ev0:  "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
  "evn 0 = True"
| "evn (Suc 0) = False"
| "evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
  apply (induction rule: ev.induct)
  by (simp_all)

lemma "evn n \<Longrightarrow> ev n"
  apply (induction n rule: evn.induct)
  by (simp_all add: ev0 evSS)

(* Just to show it can be done in one go; separating out the subgoals *)
lemma "ev n = evn n"
  apply (rule iffI)
  subgoal apply (induction rule: ev.induct) by (simp_all)
  apply (induction n rule: evn.induct) by (simp_all add: ev0 evSS)

(* ev0 and evSS (i.e. inductive rules in general) are not automatically turned into
   simp and intro rules, unlike the rules in the evn "fun" definition. This is because
   "fun" definitions have a termination requirement, but inductive definitions do not.
   In this case, they *do* make sense as such rules, so we can declare them as such: *)
declare ev.intros[simp, intro]

(* "for r" says that "r" is a "fixed" parameter of star, which lets Isabelle generate
   simpler induction rules *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl:   "star r x x"
| step:   "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
 
lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply (assumption)
  apply (metis step)
  done

(* Exercises *)

(* 4.2 *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
  empty:      "palindrome []"
| singleton:  "palindrome [x]"
| wrap:       "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
  by (simp_all)

(* 4.3 *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl':  "star' r x x"
| step':  "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_inv_step: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply (rule step[where ?y = z])
    apply (assumption)
    apply (rule refl)
  apply (metis step)
  done

lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (rule refl)
  apply (simp add: star_inv_step)
  done

lemma star'_inv_step: "r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply (rotate_tac) (* induction happens on first assumption, rotate modifies order *)
  apply (induction rule: star'.induct)
  apply (rule step'[where ?y = x])
    apply (rule refl')
    apply (assumption)
  apply (metis step')
  done

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (rule refl')
  apply (simp add: star'_inv_step)
  done

(* Ex. 4.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter_refl: "iter r 0 x x"
| iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply (induction rule: star.induct)
  apply (rule exI[where ?x = 0])
  apply (rule iter_refl)
  apply (erule exE)
  apply (rule_tac x = "Suc n" in exI)
  apply (erule iter_step)
  apply (assumption)
  done
(* The easy way: (this proofs the whole theorem after being given the induction)
  apply (auto intro: iter_refl iter_step)
  done
*)

(* Ex 4.5 *)
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  emptyS:   "S []"
| wrapS:    "S w \<Longrightarrow> S (a # w @ [b])"
| doubleS:  "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
  emptyT:   "T []"
| buildT:   "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [a] @ w2 @ [b])"

lemma TtoS: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  apply (rule emptyS)
  apply (auto intro: emptyS wrapS doubleS)
  done

lemma StoT: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
  apply (rule emptyT)
  apply (auto intro: emptyT buildT)

thm buildT

end