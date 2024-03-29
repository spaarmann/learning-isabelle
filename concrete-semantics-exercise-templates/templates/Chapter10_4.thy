theory Chapter10_4
imports "HOL-IMP.Live_True" "HOL-IMP.Vars" "Short_Theory"
begin

text\<open>
\exercise
In the context of ordinary live variable analysis, elimination of dead variables
(@{text bury}) is not idempotent (Exercise~\ref{exe:bury-not-idemp}).
Now define the textually identical function @{text bury} in the context
of true liveness analysis (theory @{short_theory "Live_True"})
and prove that it is idempotent.
\<close>

fun bury :: "com \<Rightarrow> vname set \<Rightarrow> com" where
"bury SKIP X = SKIP" |
"bury (x ::= a) X = (if x \<in> X then x ::= a else SKIP)" |
"bury (c\<^sub>1;; c\<^sub>2) X = (bury c\<^sub>1 (L c\<^sub>2 X);; bury c\<^sub>2 X)" |
"bury (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = IF b THEN bury c\<^sub>1 X ELSE bury c\<^sub>2 X" |
"bury (WHILE b DO c) X = WHILE b DO bury c (L (WHILE b DO c) X)"

text\<open> The following two tweaks improve proof automation: \<close>

declare L.simps(5)[simp]
lemmas L_mono2 = L_mono[unfolded mono_def]

text\<open> To show that @{const bury} is idempotent we need a key lemma: \<close>

lemma L_bury: "X \<subseteq> Y \<Longrightarrow> L (bury c Y) X = L c X"
(* your definition/proof here *)

text\<open> The proof is straightforward except for the case
\noquotes{@{term[source] "While b c"}} where reasoning about @{const lfp}
is required. Sledgehammer should help with the details.

Now we can prove idempotence of @{const bury}, again by induction on @{text c}:
\<close>

theorem bury_idemp: "bury (bury c X) X = bury c X"
(* your definition/proof here *)

text\<open>
Due to lemma @{thm[source] L_bury}, even the @{text While} case should be easy.
\endexercise
\<close>

end

