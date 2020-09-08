theory hw09
  imports Main "HOL-Data_Structures.RBT_Set"
begin



fun min_height :: "('a,'b) tree \<Rightarrow> nat" where
"min_height Leaf = 0" |
"min_height (Node _ l _ r) = min (min_height l) (min_height r) + 1"

definition "balanced t \<equiv> height t - min_height t \<le> 1"



fun mk_rbt :: "('a,unit) tree \<Rightarrow> 'a rbt" where
  "mk_rbt Leaf = Leaf"
| "mk_rbt (Node _ l a r) = (let
    l'=mk_rbt l;
    r'=mk_rbt r
  in
    if min_height l > min_height r then
      B (paint Red l') a r'
    else if min_height l < min_height r then
      B l' a (paint Red r')
    else
      B l' a r'
  )"


text \<open>
  \subsection*{Warmup}

\<close>

lemma balanced_subt: "balanced (Node c l a r) \<Longrightarrow> balanced l \<and> balanced r"
  unfolding balanced_def by auto


lemma aux1:"height t \<ge> min_height t"
  apply(induction t)
  by auto

lemma balanced_alt:
  "balanced t \<longleftrightarrow> height t = min_height t \<or> height t = min_height t + 1"
  unfolding balanced_def
  by (metis One_nat_def add_diff_cancel_left' aux1 cancel_comm_monoid_add_class.diff_cancel le_Suc_eq le_add_diff_inverse le_zero_eq order_refl)

text \<open>
  \subsection*{The Easy Parts}
\<close>


lemma mk_rbt_inorder: "inorder (mk_rbt t) = inorder t"
  apply(induction t)
   apply(auto)
  by (smt inorder.simps(2) inorder_paint)


lemma mk_rbt_color: "color (mk_rbt t) = Black"
  apply(induction t)
   apply(auto)
  by (smt RBT_Set.color.simps(2))

text \<open>
  \subsection*{Medium Complex Parts}

\<close>



lemma mk_rbt_bheight: "balanced t \<Longrightarrow> bheight (mk_rbt t) = min_height t"
proof(induction t)
  case Leaf
  then show ?case by auto
next
  case (Node x1 t1 x3 t2)
  note IH = Node.IH
  have "min_height t1 = min_height t2 \<or> min_height t1 < min_height t2 \<or> min_height t1 > min_height t2" (is "?C1 \<or> ?C2 \<or> ?C3")
    by auto
  moreover
  {
    assume ?C1
    have ?case using IH Node.prems \<open>?C1\<close>
      apply(cases "min_height t1")
       apply(auto)
       apply (meson balanced_subt)
      by (meson balanced_subt)
    }
    moreover
    {
      assume ?C2
      have ?case using IH Node.prems \<open>?C2\<close>
        apply(cases "min_height t1")
         apply(auto)
         apply (meson balanced_subt)
        by (metis balanced_subt min.strict_order_iff)
    }
    moreover
    {
      assume ?C3
      then have h0:"min_height (Node x1 t1 x3 t2) = min_height t2 + 1" using IH Node.prems by force
      then have h1:"min_height t2 = 0 \<Longrightarrow> bheight (paint Red (mk_rbt t1)) = 0" using IH Node.prems
        by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_leI \<open>min_height t2 < min_height t1\<close> add_diff_cancel_right' aux1 balanced_def bheight_paint_Red height.simps(2) le_trans max.commute max_def mk_rbt_color)
      then have h2: "min_height t1 > min_height t2 \<Longrightarrow> min_height t1 = Suc (min_height t2)" using IH Node.prems
        by (smt Suc_eq_plus1 Suc_leI Suc_mono balanced_alt balanced_subt h0 height.simps(2) less_Suc_eq max.commute max_def not_le)
      then have h3: " min_height t1 > min_height t2 \<Longrightarrow> bheight (paint Red (mk_rbt t1)) = min_height t2" using IH Node.prems
        apply(cases "min_height t1")
         apply(auto)
        by (metis Suc_eq_plus1 add_diff_cancel_right' balanced_subt bheight_paint_Red mk_rbt_color)
        
      then have ?case using IH Node.prems \<open>?C3\<close> 
        apply(cases "min_height t2")
        by (auto)
        
      }
      ultimately show ?case by blast
qed


lemma mk_rbt_invh: "balanced t \<Longrightarrow> invh (mk_rbt t)"
  apply(induction t rule:mk_rbt.induct)
   apply(simp add: balanced_alt mk_rbt_color mk_rbt_inorder mk_rbt_bheight)
  apply(simp split:if_splits)
  by (smt Suc_eq_plus1 Suc_le_mono add_diff_cancel_right' antisym_conv balanced_alt balanced_subt bheight_paint_Red height.simps(2) invh.simps(2) le_Suc_eq le_simps(3) max_def min_def invh_paint min_height.simps(2) mk_rbt_bheight mk_rbt_color)






fun mk_rbt' :: "('a,unit) tree \<Rightarrow> 'a rbt \<times> nat"
where
  "mk_rbt' Leaf = (Leaf, 0)"
| "mk_rbt' (Node _ l a r) = (let
    (l',lx)=mk_rbt' l;
    (r',rx)=mk_rbt' r
  in
    if lx > rx then
      (B (paint Red l') a r', Suc(rx))
    else if lx < rx then
      (B l' a (paint Red r'), Suc(lx))
    else
      (B l' a r', Suc(lx))
  )" 

lemma mk_rbt'_refine_aux: "mk_rbt' t = (mk_rbt t, min_height t)"
  apply(induction t)
  apply(auto)
  done


lemma mk_rbt'_refine: "fst (mk_rbt' t) = mk_rbt t"
  apply(induction t)
  by(auto simp:mk_rbt'_refine_aux)



end
