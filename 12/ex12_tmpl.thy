(*<*)
theory ex12_tmpl
imports
  Complex_Main
  "HOL-Library.Multiset"
begin
(*>*)
text {* \ExerciseSheet{12}{29.~6.~2018} *}

text \<open>
  \Exercise{Sparse Binary Numbers}

  Implement operations carry, inc, and add on sparse binary numbers,
  analogously to the operations link, ins, and meld on binomial heaps.

  Show that the operations have logarithmic worst-case complexity.
\<close>

type_synonym rank = nat
type_synonym snat = "rank list"

abbreviation invar :: "snat \<Rightarrow> bool" where "invar s \<equiv> sorted_wrt op< s"
definition \<alpha> :: "snat \<Rightarrow> nat" where "\<alpha> s = (\<Sum>i\<leftarrow>s. 2^i)"

lemmas [simp] = sorted_wrt_Cons sorted_wrt_append


fun carry :: "rank \<Rightarrow> snat \<Rightarrow> snat"
  where
  "carry _ _ = undefined"

lemma carry_invar[simp]: specify_something_meaningful oops

lemma carry_\<alpha>: specify_something_meaningful oops


definition inc :: "snat \<Rightarrow> snat" where "inc \<equiv> undefined"

lemma inc_invar[simp]: "invar rs \<Longrightarrow> invar (inc rs)" sorry

lemma inc_\<alpha>[simp]: "invar rs \<Longrightarrow> \<alpha> (inc rs) = Suc (\<alpha> rs)" sorry

fun add :: "snat \<Rightarrow> snat \<Rightarrow> snat"
  where
  "add _ _ = undefined"


lemma add_invar[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "invar (add rs\<^sub>1 rs\<^sub>2)"
  sorry

lemma add_\<alpha>[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "\<alpha> (add rs\<^sub>1 rs\<^sub>2) = \<alpha> rs\<^sub>1 + \<alpha> rs\<^sub>2"
  sorry


(** Size in relation to represented number *)
lemma size_snat:
  assumes "invar rs"
  shows "2^length rs \<le> \<alpha> rs + 1"
  sorry


(** Timing *)

fun t_carry :: "rank \<Rightarrow> snat \<Rightarrow> nat"
  where
  "t_carry _ _ = undefined"

definition t_inc :: "snat \<Rightarrow> nat"
  where "t_inc rs = undefined"

lemma t_inc_bound:
  assumes "invar rs"
  shows "t_inc rs \<le> log 2 (\<alpha> rs + 1) + 1"
  sorry

fun t_add :: "snat \<Rightarrow> snat \<Rightarrow> nat"
  where
  "t_add _ _ = undefined"


lemma t_add_bound:
  fixes rs\<^sub>1 rs\<^sub>2
  defines "n\<^sub>1 \<equiv> \<alpha> rs\<^sub>1"
  defines "n\<^sub>2 \<equiv> \<alpha> rs\<^sub>2"
  assumes INVARS: "invar rs\<^sub>1" "invar rs\<^sub>2"
  shows "t_add rs\<^sub>1 rs\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
  sorry


(*<*)
end
(*>*)
