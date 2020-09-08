(*<*)
theory ex12
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


(*<*)
lemma \<alpha>_Nil[simp]: "\<alpha> [] = 0"
  unfolding \<alpha>_def by auto

lemma \<alpha>_Cons[simp]: "\<alpha> (r#rs) = 2^r + \<alpha> rs"
  unfolding \<alpha>_def by auto

lemma \<alpha>_append[simp]: "\<alpha> (rs\<^sub>1@rs\<^sub>2) = \<alpha> rs\<^sub>1 + \<alpha> rs\<^sub>2"
  unfolding \<alpha>_def by auto

(*>*)

fun carry :: "rank \<Rightarrow> snat \<Rightarrow> snat"
(*<*)
  where
  "carry r [] = [r]"
| "carry r (r'#rest) = (if r<r' then r#r'#rest else carry (r+1) rest)"
(*>*)

lemma carry_invar[simp]:
(*<*)
  assumes "invar rs"
  shows "invar (carry r rs)"
  using assms
  apply (induction r rs rule: carry.induct)
  apply (auto)
  done
(*>*)

lemma carry_\<alpha>:
(*<*)
  assumes "invar rs"
  assumes "\<forall>r'\<in>set rs. r\<le>r'"
  shows "\<alpha> (carry r rs) = 2^r + \<alpha> rs"
  using assms
  by (induction r rs rule: carry.induct) force+
(*>*)

(*<*)
lemma carry_rank_bound:
  assumes "r' \<in> set (carry r rs)"
  assumes "\<forall>r'\<in>set rs. r\<^sub>0 < r'"
  assumes "r\<^sub>0 < r"
  shows "r\<^sub>0 < r'"
  using assms
  by (induction r rs rule: carry.induct) (auto split: if_splits)
(*>*)


definition inc :: "snat \<Rightarrow> snat"
(*<*)
  where "inc rs = carry 0 rs"
(*>*)

lemma inc_invar[simp]: "invar rs \<Longrightarrow> invar (inc rs)"
(*<*)
  unfolding inc_def by auto
(*>*)

lemma inc_\<alpha>[simp]: "invar rs \<Longrightarrow> \<alpha> (inc rs) = Suc (\<alpha> rs)"
(*<*)
  unfolding inc_def by (auto simp: carry_\<alpha>)
(*>*)

fun add :: "snat \<Rightarrow> snat \<Rightarrow> snat"
(*<*)
  where
  "add rs [] = rs"
| "add [] rs = rs"
| "add (r\<^sub>1#rs\<^sub>1) (r\<^sub>2#rs\<^sub>2) = (
    if r\<^sub>1 < r\<^sub>2 then r\<^sub>1#add rs\<^sub>1 (r\<^sub>2#rs\<^sub>2)
    else if r\<^sub>2<r\<^sub>1 then r\<^sub>2#add (r\<^sub>1#rs\<^sub>1) rs\<^sub>2
    else carry (r\<^sub>1 + 1) (add rs\<^sub>1 rs\<^sub>2)
    )"
(*>*)

(*<*)
lemma add_rank_bound:
  assumes "r' \<in> set (add rs\<^sub>1 rs\<^sub>2)"
  assumes "\<forall>r'\<in>set rs\<^sub>1. r < r'"
  assumes "\<forall>r'\<in>set rs\<^sub>2. r < r'"
  shows "r < r'"
  using assms
  apply (induction rs\<^sub>1 rs\<^sub>2 arbitrary: r' rule: add.induct)
  apply (auto split: if_splits simp: carry_rank_bound)
  done
(*>*)

lemma add_invar[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "invar (add rs\<^sub>1 rs\<^sub>2)"
(*<*)
  using assms
proof (induction rs\<^sub>1 rs\<^sub>2 rule: add.induct)
  case (3 r\<^sub>1 rs\<^sub>1 r\<^sub>2 rs\<^sub>2)

  consider (LT) "r\<^sub>1 < r\<^sub>2"
         | (GT) "r\<^sub>1 > r\<^sub>2"
         | (EQ) "r\<^sub>1 = r\<^sub>2"
    using antisym_conv3 by blast
  then show ?case proof cases
    case LT
    then show ?thesis using 3
      by (force elim!: add_rank_bound)
  next
    case GT
    then show ?thesis using 3
      by (force elim!: add_rank_bound)
  next
    case [simp]: EQ

    from "3.IH"(3) "3.prems" have [simp]: "invar (add rs\<^sub>1 rs\<^sub>2)"
      by auto

    have "r\<^sub>2 < r'" if "r' \<in> set (add rs\<^sub>1 rs\<^sub>2)" for r'
      using that
      apply (rule add_rank_bound)
      using "3.prems" by auto
    with EQ show ?thesis by auto
  qed
qed simp_all
(*>*)

lemma add_\<alpha>[simp]:
  assumes "invar rs\<^sub>1"
  assumes "invar rs\<^sub>2"
  shows "\<alpha> (add rs\<^sub>1 rs\<^sub>2) = \<alpha> rs\<^sub>1 + \<alpha> rs\<^sub>2"
(*<*)
  using assms
  apply (induction rs\<^sub>1 rs\<^sub>2 rule: add.induct)
  apply (auto simp: carry_\<alpha> Suc_leI add_rank_bound)
  done
(*>*)


lemma size_snat:
  assumes "invar rs"
  shows "2^length rs \<le> \<alpha> rs + 1"
(*<*)
proof -
  have "(2::nat)^length rs = (\<Sum>i\<in>{0..<length rs}. 2^i) + 1"
    by (simp add: sum_power2)
  also have "\<dots> \<le> \<alpha> rs + 1"
    using assms unfolding \<alpha>_def
    by (simp add: sorted_wrt_less_sum_mono_lowerbound)
  finally show ?thesis .
qed
(*>*)

fun t_carry :: "rank \<Rightarrow> snat \<Rightarrow> nat"
(*<*)
  where
  "t_carry r [] = 1"
| "t_carry r (r'#rest) = (if r<r' then 1 else 1 + t_carry (r+1) rest)"
(*>*)

definition t_inc :: "snat \<Rightarrow> nat"
(*<*)
  where "t_inc rs = t_carry 0 rs"
(*>*)

lemma t_inc_bound:
  assumes "invar rs"
  shows "t_inc rs \<le> log 2 (\<alpha> rs + 1) + 1"
(*<*)
proof -
  have "t_carry r rs \<le> length rs + 1" for r
    by (induction r rs rule: t_carry.induct) auto
  hence "t_inc rs \<le> length rs + 1" unfolding t_inc_def by auto
  hence "(2::nat)^t_inc rs \<le> 2^(length rs + 1)"
    by (rule power_increasing) auto
  also have "\<dots> \<le> 2*(\<alpha> rs + 1)" using size_snat[OF \<open>invar rs\<close>] by auto
  finally have "2 ^ t_inc rs \<le> 2 * (\<alpha> rs + 1)" .
  from le_log2_of_power[OF this] show ?thesis
    by (simp only: log_mult of_nat_mult) auto
qed
(*>*)

fun t_add :: "snat \<Rightarrow> snat \<Rightarrow> nat"
(*<*)
  where
  "t_add rs [] = 1"
| "t_add [] rs = 1"
| "t_add (r\<^sub>1#rs\<^sub>1) (r\<^sub>2#rs\<^sub>2) = 1 + (
    if r\<^sub>1 < r\<^sub>2 then t_add rs\<^sub>1 (r\<^sub>2#rs\<^sub>2)
    else if r\<^sub>2<r\<^sub>1 then t_add (r\<^sub>1#rs\<^sub>1) rs\<^sub>2
    else t_carry (r\<^sub>1 + 1) (add rs\<^sub>1 rs\<^sub>2) + t_add rs\<^sub>1 rs\<^sub>2
    )"
(*>*)

(*<*)
lemma l_carry_estimate:
  "t_carry r rs + length (carry r rs) = 2 + length rs"
  by (induction r rs rule: carry.induct) auto

lemma l_add_estimate:
  "length (add rs\<^sub>1 rs\<^sub>2) + t_add rs\<^sub>1 rs\<^sub>2 \<le> 2 * (length rs\<^sub>1 + length rs\<^sub>2) + 1"
  apply (induction rs\<^sub>1 rs\<^sub>2 rule: t_add.induct)
  apply (auto simp: l_carry_estimate algebra_simps)
  done
(*>*)

lemma t_add_bound:
  fixes rs\<^sub>1 rs\<^sub>2
  defines "n\<^sub>1 \<equiv> \<alpha> rs\<^sub>1"
  defines "n\<^sub>2 \<equiv> \<alpha> rs\<^sub>2"
  assumes INVARS: "invar rs\<^sub>1" "invar rs\<^sub>2"
  shows "t_add rs\<^sub>1 rs\<^sub>2 \<le> 4*log 2 (n\<^sub>1 + n\<^sub>2 + 1) + 2"
(*<*)
proof -
  define n where "n = n\<^sub>1 + n\<^sub>2"

  from l_add_estimate[of rs\<^sub>1 rs\<^sub>2]
  have "t_add rs\<^sub>1 rs\<^sub>2 \<le> 2 * (length rs\<^sub>1 + length rs\<^sub>2) + 1" by auto
  hence "(2::nat)^t_add rs\<^sub>1 rs\<^sub>2 \<le> 2^(2 * (length rs\<^sub>1 + length rs\<^sub>2) + 1)"
    by (rule power_increasing) auto
  also have "\<dots> = 2*(2^length rs\<^sub>1)\<^sup>2*(2^length rs\<^sub>2)\<^sup>2"
    by (auto simp: algebra_simps power_add power_mult)
  also note INVARS(1)[THEN size_snat]
  also note INVARS(2)[THEN size_snat]
  finally have "2 ^ t_add rs\<^sub>1 rs\<^sub>2 \<le> 2 * (n\<^sub>1 + 1)\<^sup>2 * (n\<^sub>2 + 1)\<^sup>2"
    by (auto simp: power2_nat_le_eq_le n\<^sub>1_def n\<^sub>2_def)
  from le_log2_of_power[OF this] have "t_add rs\<^sub>1 rs\<^sub>2 \<le> log 2 \<dots>"
    by simp
  also have "\<dots> = log 2 2 + 2*log 2 (n\<^sub>1 + 1) + 2*log 2 (n\<^sub>2 + 1)"
    by (simp add: log_mult log_nat_power)
  also have "n\<^sub>2 \<le> n" by (auto simp: n_def)
  finally have "t_add rs\<^sub>1 rs\<^sub>2 \<le> log 2 2 + 2*log 2 (n\<^sub>1 + 1) + 2*log 2 (n + 1)"
    by auto
  also have "n\<^sub>1 \<le> n" by (auto simp: n_def)
  finally have "t_add rs\<^sub>1 rs\<^sub>2 \<le> log 2 2 + 4*log 2 (n + 1)"
    by auto
  also have "log 2 2 \<le> 2" by auto
  finally have "t_add rs\<^sub>1 rs\<^sub>2 \<le> 4*log 2 (n + 1) + 2" by auto
  thus ?thesis unfolding n_def by (auto simp: algebra_simps)
qed
(*>*)



(*<*)
end
(*>*)
