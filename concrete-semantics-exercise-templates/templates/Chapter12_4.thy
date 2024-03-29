theory Chapter12_4
imports "HOL-IMP.VCG" "HOL-IMP.Hoare_Examples" "Short_Theory"
begin

text\<open>
\exercise
Let @{term "asum i"} be the annotated command \texttt{y := 0; W}
where \texttt{W} is defined in Example~12.7. Prove
\<close>
(* your definition of asum here *)

lemma "\<turnstile> {\<lambda>s. s ''x'' = i} strip(asum i) {\<lambda>s. s ''y'' = sum i}"
(* your definition/proof here *)

text\<open>
with the help of corollary @{thm[source] vc_sound'}.
\endexercise

\exercise
Solve exercises \ref{exe:Hoare:sumeq} to \ref{exe:Hoare:sqrt} using the VCG:
for every Hoare triple @{prop"\<turnstile> {P} c {Q}"} from one of those exercises
define an annotated version @{text C} of @{text c} and prove
@{prop"\<turnstile> {P} strip C {Q}"} with the help of %Corollary~\ref{cor:vc_sound}
corollary @{thm[source] vc_sound'}.
\<close>

text\<open>
\endexercise

\exercise
Having two separate functions @{const pre} and @{const vc} is inefficient.
When computing @{const vc} one often needs to compute @{const pre} too,
leading to multiple traversals of many subcommands. Define an optimised function
\<close>
fun prevc :: "acom \<Rightarrow> assn \<Rightarrow> assn \<times> bool" where
(* your definition/proof here *)

text\<open> that traverses the command only once. Prove \<close>

lemma "prevc C Q = (pre C Q, vc C Q)"
(* your definition/proof here *)

text\<open>
\endexercise

\exercise
Design a VCG that computes post rather than preconditions.
Start by solving Exercise~\ref{exe:fwdassign}. Now modify theory
@{short_theory "VCG"} as follows. Instead of @{const pre} define a function
\<close>

fun post :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
(* your definition/proof here *)

text\<open>
such that (with the execption of loops) @{term "post C P"} is the strongest
postcondition of @{text C} w.r.t.\ the precondition @{text P} (see also
Exercise~\ref{exe:sp}). Now modify @{const vc} such that is uses
@{const post} instead of @{const pre} and prove its soundness
and completeness.
\<close>

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
(* your definition/proof here *)

lemma vc_sound: "vc C P \<Longrightarrow> \<turnstile> {P} strip C {post C P}"
(* your definition/proof here *)



lemma vc_complete: "\<turnstile> {P} c {Q}
  \<Longrightarrow> \<exists>C. strip C = c \<and> vc C P \<and> (\<forall>s. post C P s \<longrightarrow> Q s)"
(* your definition/proof here *)

text \<open>
\endexercise
\<close>

end

