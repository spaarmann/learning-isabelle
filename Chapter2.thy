theory Chapter2
  imports Main
begin

section "Chapter 2.2"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

lemma add_02 [simp]: "add m 0 = m"
  apply (induction m)
  apply (auto)
  done

datatype 'a my_list = Nil | Cons 'a "'a my_list"

fun app :: "'a my_list \<Rightarrow> 'a my_list \<Rightarrow> 'a my_list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun my_rev :: "'a my_list \<Rightarrow> 'a my_list" where
  "my_rev Nil = Nil"
| "my_rev (Cons x xs) = app (my_rev xs) (Cons x Nil)"

lemma app_Nil2 [simp]: "app xs Nil = xs"
  apply (induction xs)
  apply (auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
  apply (auto)
  done

lemma my_rev_app [simp]: "my_rev (app xs ys) = app (my_rev ys) (my_rev xs)"
  apply (induction xs)
  apply (auto)
  done

(* [simp] means that, when proven, this theorem can be used as a simplification rule in future proofs *)
theorem my_rev_my_rev [simp]: "my_rev (my_rev xs) = xs"
  apply (induction xs)
  apply (auto)
  done

(* Exercises *)

(* 2.1 *)
value "1 + (2 :: nat)"
value "1 + (1 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"

(* 2.2 *)
lemma add_assoc [simp]: "add m (add n k) = add (add m n) k"
  apply (induction m)
  apply (auto)
  done

lemma add_one [simp]: "add n (Suc 0) = Suc n"
  apply (induction n)
   apply (auto)
  done

lemma add_suc [simp]: "add n (Suc m) = Suc (add n m)"
  apply (induction n)
   apply (auto)
  done

lemma add_comm [simp]: "add m n = add n m"
  apply (induction m)
   apply (auto)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double (Suc m) = Suc (Suc (double m))"

lemma double_add: "double m = add m m"
  apply (induction m)
   apply (auto)
  done

(* 2.3 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0"
(* using this definition, "auto" can't immediately do the proof below, but using the second one it can *)
(* see count2 below for how to make the proof work with the first version! It's because the simplifier
   won't expand the let by default, but we can make it do that! *)
(*| "count x (y # xs) = (let c = (count x xs) in (if x = y then (Suc c) else c))" *)
| "count x (y # xs) = (if x = y then (Suc (count x xs)) else (count x xs))"

value "count (1 :: nat) [1,1,1,1,2,3,4]"
value "count (0 :: nat) []"
value "count (5 :: nat) [1,1,33,3]"

lemma count_len: "count x xs \<le> length xs"
  apply (induction xs)
   apply (auto)
  done

fun count2 :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count2 x [] = 0"
| "count2 x (y # xs) = (let c = (count2 x xs) in (if x = y then (Suc c) else c))"

lemma "count2 x xs \<le> length xs"
  apply (induction xs)
  apply (auto simp add: Let_def)
  done

(* 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]"
| "snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc_cons [simp]: "reverse (snoc xs x) = x # (reverse xs)"
  apply (induction xs)
   apply (auto)
  done

lemma reverse_reverse: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto)
  done

(* 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = (Suc n) + (sum_upto n)"

lemma gauss: "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply (auto)
  done


section "Chapter 2.3"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip"
| "mirror (Node l a r) = Node (mirror r) a (mirror l)"

(* Exercises *)

(* 2.6 *)

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"
| "contents (Node l a r) = contents l @ (a # contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0"
| "sum_tree (Node l n r) = sum_tree l + n + sum_tree r"

lemma sum_tree_sum_contents: "sum_tree t = sum_list (contents t)"
  apply (induction t)
   apply (auto)
  done

(* 2.7 *)
fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Tip = []"
| "pre_order (Node l a r) = a # (pre_order l @ pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Tip = []"
| "post_order (Node l a r) = post_order l @ post_order r @ [a]"

lemma pre_post_order: "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
   apply (auto)
  done

(* 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []"
| "intersperse a [x] = [x]"
| "intersperse a (x1 # x2 # xs) = [x1, a, x2] @ intersperse a xs"

lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply (auto)
  done

section "Chapter 2.4"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys"
| "itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply (auto)
  done

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0        n = n"
| "itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = add m n"
  apply (induction m arbitrary: n)
   apply (auto)
  done

section "Chapter 2.5"

(* Exercises *)

(* 2.10 *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1"
| "nodes (Node l r) = Suc (nodes l + nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"
| "explode (Suc n) t = explode n (Node t t)"

lemma "nodes (explode n t) = 2^n * nodes t + (2^n - 1)"
  apply (induction n arbitrary: t)
   apply (auto simp add: algebra_simps)
  done

(* 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x"
| "eval (Const c) _ = c"
| "eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)"
| "eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0"
| "evalp (c#cs) x = c + x * evalp cs x"

fun sump :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "sump [] bs = bs"
| "sump as [] = as"
| "sump (a#as) (b#bs) = (a + b)#(sump as bs)"

fun mulp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mulp [] bs = []"
| "mulp (a#as) bs = sump (map ((*) a) bs) (0#(mulp as bs))"

(* (2 + 3x) * (4 + 1x) = 2*4 + 2*1x + 3*4x + 3*1*x*x = 8 + 14x + 3x^2 *)
value "mulp [2, 3] [4, 1]"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"
| "coeffs (Const c) = [c]"
| "coeffs (Add e1 e2) = sump (coeffs e1) (coeffs e2)"
| "coeffs (Mult e1 e2) = mulp (coeffs e1) (coeffs e2)"

lemma evalp_add [simp]: "evalp (sump as bs) x = evalp as x + evalp bs x"
  apply (induction as bs rule: sump.induct)
    apply (auto simp add: algebra_simps)
  done

lemma evalp_scalar_mult [simp]: "evalp (map ((*) a) bs) x = a * evalp bs x"
  apply (induction bs)
   apply (auto simp add: algebra_simps)
  done

lemma evalp_mult [simp]: "evalp (mulp as bs) x = evalp as x * evalp bs x"
  apply (induction as bs rule: mulp.induct)
   apply (auto simp add: algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply (induction e)
     apply (auto simp add: algebra_simps)
  done

end