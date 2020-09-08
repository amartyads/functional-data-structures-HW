(*<*)
theory hw09tmpl
  imports Main "HOL-Data_Structures.RBT_Set"
begin
(*>*)

text \<open>\NumHomework{Balanced Tree to RBT}{15.~6.~2018}

  A tree is balanced, if its minimum height and its height differ by at most 1.
\<close>

fun min_height :: "('a,'b) tree \<Rightarrow> nat" where
"min_height Leaf = 0" |
"min_height (Node _ l _ r) = min (min_height l) (min_height r) + 1"

definition "balanced t \<equiv> height t - min_height t \<le> 1"

text \<open>The following function paints a balanced tree to form a valid red-black tree
  with the same structure. The task of this homework is to prove this!
\<close>

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

  Show that the left and right subtree of a balanced tree are, again, balanced
\<close>

lemma balanced_subt: "balanced (Node c l a r) \<Longrightarrow> balanced l \<and> balanced r"
  unfolding balanced_def by auto


text \<open>Show the following alternative characterization of balanced:\<close>

lemma aux1:"height t \<ge> min_height t"
  apply(induction t)
  by auto

lemma balanced_alt:
  "balanced t \<longleftrightarrow> height t = min_height t \<or> height t = min_height t + 1"
  text \<open>Hint: Auxiliary lemma relating @{term \<open>height t\<close>} and @{term \<open>min_height t\<close>}\<close>
  unfolding balanced_def
  by (metis One_nat_def add_diff_cancel_left' aux1 cancel_comm_monoid_add_class.diff_cancel le_Suc_eq le_add_diff_inverse le_zero_eq order_refl)

text \<open>
  \subsection*{The Easy Parts}

  Show that \<open>mk_rbt\<close> does not change the inorder-traversal
\<close>
lemma mk_rbt_inorder: "inorder (mk_rbt t) = inorder t"
  apply(induction t)
   apply(auto)
  by (smt inorder.simps(2) inorder_paint)

text \<open>Show that the color of the root node is always black\<close>
lemma mk_rbt_color: "color (mk_rbt t) = Black"
  apply(induction t)
   apply(auto)
  by (smt RBT_Set.color.simps(2))

text \<open>
  \subsection*{Medium Complex Parts}

  Show that the black-height of the returned tree is the minimum height of the argument tree
\<close>



lemma mk_rbt_bheight: "balanced t \<Longrightarrow> bheight (mk_rbt t) = min_height t"
text \<open>Hint: Use Isar to have better control when to unfold with @{thm [source] balanced_alt},
  and when to use @{thm [source] balanced_subt} (e.g. to discharge the premises of the IH)
\<close>
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

text \<open>
  Show that the returned tree satisfies the height invariant.
\<close>

lemma mk_rbt_invh: "balanced t \<Longrightarrow> invh (mk_rbt t)"
  apply(induction t rule:mk_rbt.induct)
   apply(simp add: balanced_alt mk_rbt_color mk_rbt_inorder mk_rbt_bheight)
  apply(simp split:if_splits)
  by (smt Suc_eq_plus1 Suc_le_mono add_diff_cancel_right' antisym_conv balanced_alt balanced_subt bheight_paint_Red height.simps(2) invh.simps(2) le_Suc_eq le_simps(3) max_def min_def invh_paint min_height.simps(2) mk_rbt_bheight mk_rbt_color)


text \<open>
  \subsection*{The Hard Part (3 Bonus Points)}

  For {\bf three bonus points}, show that the returned tree satisfies the color invariant.

  Warning: This requires careful case splitting, via a clever combination of
    automation and manual proof (Isar, aux-lemmas), in order to deal with the
    multiple cases without a combinatorial explosion of the proofs.
\<close>

lemma mk_rbt_invc: "balanced t \<Longrightarrow> invc (mk_rbt t)"
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
        apply (meson balanced_subt)
       apply (meson balanced_subt)
      by (meson balanced_subt)
  }
  moreover
  {
    assume ?C2
    then have h0:"min_height (Node x1 t1 x3 t2) = min_height t1 + 1" using IH Node.prems by force
    then have h1: "min_height t1 < min_height t2 \<Longrightarrow> min_height t2 = Suc (min_height t1)" using IH Node.prems
      by (smt Suc_eq_plus1 Suc_leI Suc_mono balanced_alt balanced_subt h0 height.simps(2) less_Suc_eq max.commute max_def not_le)
    then have h2:"invc (paint Red (mk_rbt t2))" using IH Node.prems sorry
      then have ?case using IH Node.prems \<open>?C2\<close> 
      apply(cases "min_height t1")
        apply(auto)
           apply (smt balanced_subt)
          apply (simp add: h2)
        by (meson balanced_subt)
    }

qed


(* Now you can combine everything, to show that you are, indeed, generating an RBT *)
theorem mk_rbt_is_rbt: "balanced t \<Longrightarrow> rbt (mk_rbt t)"
  using mk_rbt_invh mk_rbt_invc mk_rbt_color unfolding rbt_def by auto



text \<open>\NumHomework{Linear-Time Repainting}{15.~6.~2018}

  Write a linear-time version of \<open>mk_rbt\<close>, and show that it behaves like
  \<open>mk_rbt\<close>.

  Idea: Compute the min-height during the same recursion as you build
    the tree.

  Note: No formal complexity proof required.
\<close>

fun mk_rbt' :: "('a,unit) tree \<Rightarrow> 'a rbt \<times> nat" -- \<open>Returns the RBT and the min-height of the argument\<close>
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



(*<*)
end
(*>*)
