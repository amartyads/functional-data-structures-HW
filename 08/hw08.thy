theory hw08
  imports Complex_Main "HOL-Library.Tree"
begin

fun fib :: "nat \<Rightarrow> nat"
  where
    fib0: "fib 0 = 0"
  | fib1: "fib (Suc 0) = 1"
  | fib2: "fib (Suc (Suc n)) = fib (Suc n) + fib n"

lemma f_alt_induct [consumes 1, case_names 1 2 rec]:
  assumes "n > 0"
      and "P (Suc 0)" "P 2" "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))"
  shows   "P n"
  using assms(1)
proof (induction n rule: fib.induct)
  case (3 n)
  thus ?case using assms by (cases n) (auto simp: eval_nat_numeral)
qed (auto simp: \<open>P (Suc 0)\<close> \<open>P 2\<close>)

lemma fib_lowerbound: "n > 0 \<Longrightarrow> real (fib n) \<ge> 1.5 ^ n / 3"
proof (induction n rule: f_alt_induct)
case 1
then show ?case by auto
next
  case 2
  then show ?case by (auto simp:eval_nat_numeral)
next
  case (rec n)
  then show ?case by auto
qed




fun avl :: "'a tree \<Rightarrow> bool"
where
  "avl (Node l _ r) = ((((height r::int) -(height l::int))\<in> {-1..1})\<and> avl l \<and> avl r)"
| "avl (Leaf) = True"

value "avl \<langle>\<langle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>\<rangle>"

fun avl_minnodes_height::"nat \<Rightarrow> nat"
  where
  "avl_minnodes_height 0 = 1"
| "avl_minnodes_height (Suc 0) = 2"
| "avl_minnodes_height (Suc (Suc n)) = avl_minnodes_height n + avl_minnodes_height (Suc n)"


value "height \<langle>\<langle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>"
value "size1 \<langle>\<langle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>"

value "height \<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>"
value "size1  \<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>"

value "height \<langle>\<rangle>"
value "size1  \<langle>\<rangle>"

value "height \<langle>\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>"
value "size1 \<langle>\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>"
value "avl \<langle>\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>,a,\<langle>\<langle>\<rangle>,a,\<langle>\<rangle>\<rangle>\<rangle>"

lemma avl_size: " size1 (Node t1 x t2) = size1 t1 + size1 t2"
  by simp

lemma avl_min_mono: "avl_minnodes_height n \<le> avl_minnodes_height (Suc n)"
  apply(induction n rule: avl_minnodes_height.induct)
    apply(auto)
  done


lemma min_corr: "avl t \<Longrightarrow> height t = h \<Longrightarrow> avl_minnodes_height h  \<le> size1 t"
proof(induction t arbitrary:h)
  case Leaf
  then show ?case by auto
next
  case (Node t1 x2 t2)
  note IH = Node.IH[OF _ refl]
    have "height t1 = height t2 \<or> height t1 < height t2 \<or> height t1 > height t2" (is "?C1 \<or> ?C2 \<or> ?C3")
    by auto
  moreover {
    assume ?C1
    have ?case using IH Node.prems \<open>?C1\<close>
      apply (cases "height t2")
       apply (auto)
      by (meson add_mono_thms_linordered_semiring(1) avl_min_mono le_trans)

  } moreover {
    assume ?C2 
    have "h = Suc (height t2)" using IH Node.prems  using \<open>?C2\<close> by force
    then  have ?case using IH Node.prems \<open>?C2\<close>
      apply (cases "height t2")
       apply (auto)
      by (simp add: le_less_Suc_eq)
      
  } moreover {
    assume ?C3 
     have "h = Suc (height t1)" using IH Node.prems  using \<open>?C3\<close> by force
    then  have ?case using IH Node.prems \<open>?C3\<close>
      apply (cases "height t1")
       apply (auto)
      by (simp add: le_less_Suc_eq)
  } ultimately show ?case by blast
 
qed

  


lemma fib_min: "fib (h+2)  = avl_minnodes_height h"
  apply(induction h rule:avl_minnodes_height.induct)
    apply(auto)
  done

lemma avl_fib_bound: "avl t \<Longrightarrow> height t = h \<Longrightarrow> fib (h+2) \<le> size1 t"
  using fib_min le_trans min_corr by metis
  


lemma avl_lowerbound:
  assumes "avl t"
  shows "1.5 ^ (height t + 2) / 3 \<le> real (size1 t)"
proof -
  show ?thesis using assms fib_min le_trans min_corr fib_lowerbound
    by (smt add_gr_0 avl_fib_bound of_nat_le_iff pos2)
qed







end