theory Chapter5
  imports Main
begin

section \<open>Chapter 5.3\<close>

(* Exercises *)

(* Ex 5.1 *)
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof -
  have "T x y \<or> T y x" using T by auto
  then show "T x y"
  proof
    assume "T x y"
    then show "T x y" by auto
  next
    assume "T y x"
    hence "A y x" using TA by auto
    hence "x = y" using A and assms by auto
    thus "T x y" using \<open>T y x\<close> by auto
  qed
qed

lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  hence "T y x" using T by auto
  hence "A y x" using TA by auto
  hence "x = y" using \<open>A x y\<close> and A by auto
  thus "False" using \<open>T y x\<close> and \<open>\<not> T x y\<close> by auto
qed

(* Ex 5.2 *)
lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain k where k_def: "2 * k = length xs" by auto
  obtain ys where ys_def: "ys = take k xs" by auto
  obtain zs where zs_def: "zs = drop k xs" by auto
  have "xs = ys @ zs" by (simp add: ys_def zs_def)
  moreover have "length ys = k" using k_def and ys_def by auto
  moreover have "length zs = k" using k_def and zs_def by auto
  ultimately show ?thesis by metis
next
  assume "odd (length xs)"
  then obtain k where k_def: "2 * k + 1 = length xs" by (metis oddE)
  obtain ys where ys_def: "ys = take (k + 1) xs" by auto
  obtain zs where zs_def: "zs = drop (k + 1) xs" by auto
  have "xs = ys @ zs" by (simp add: ys_def zs_def)
  moreover have "length ys = k + 1" using k_def and ys_def by auto
  moreover have "length zs = k" using k_def and zs_def by auto
  ultimately show ?thesis by metis
qed

section \<open>Chapter 5.4\<close>

lemma "length (tl xs) = length xs - 1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
next
  case (Cons y ys)
  thus ?thesis by simp
qed

(* Ex 5.3 *)
inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0"
| evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"
  
lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof -
  show ?thesis using a
  proof cases
    case evSS
    thus ?thesis by auto
  qed
qed

(* Ex 5.4 *)
lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?P")
proof
  assume ?P
  hence "ev (Suc 0)" by cases
  thus "False" by cases
qed

(* Ex 5.5 *)
inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl:   "star r x x"
| step:   "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  iter_refl: "iter r 0 x x"
| iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case (iter_refl x)
  then show ?case by (rule refl)
next
  case (iter_step x y n z)
  then show ?case by (simp add: step)
qed

(* Ex 5.6 *)
fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}"
| "elems (x#xs) = {x} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  hence "False" by auto
  then show ?case by auto
next
  case (Cons a xs)
  show ?case proof cases
    assume "x = a"
    obtain ys where ys: "(ys :: 'a list) = []" by auto
    obtain zs where zs: "zs = xs" by auto
    have "x \<notin> elems ys" using ys by auto
    thus ?case using ys zs and \<open>x = a\<close> by blast
  next
    assume "x \<noteq> a"
    hence "x \<in> elems xs" using Cons.prems by auto
    then obtain ys zs ys_ih where
      "ys = a # ys_ih" "xs = ys_ih @ x # zs" "x \<notin> elems ys_ih"
      using Cons.IH by auto
    hence "a#xs = ys @ x # zs \<and> x \<notin> elems ys" using \<open>x \<noteq> a\<close> by auto
    thus ?case by auto
  qed
qed


end