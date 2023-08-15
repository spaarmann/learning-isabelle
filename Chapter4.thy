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

end