(*<*)
theory ex09_2tmpl
imports
  "~~/src/HOL/Data_Structures/Tree23_Set"
begin
(*>*)

text \<open>\Exercise{Joining 2-3-Trees}

  Write a join function for 2-3-trees: The function shall take two
  2-3-trees \<open>l\<close> and \<open>r\<close> and an element \<open>x\<close>, and return a new 2-3-tree with
  the inorder-traversal \<open>l x r\<close> .

  Write two functions, one for the height of \<open>l\<close> being greater, the
  other for the height of \<open>r\<close> being greater.
\<close>

text \<open>\<open>height l\<close> greater\<close>
fun joinR :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i"
where
  "joinR l x r = (
    if height l = height r then Up\<^sub>i l x r
    else case l of
      Node2 l1 a l2 \<Rightarrow> (case joinR l2 x r of
        T\<^sub>i t \<Rightarrow> T\<^sub>i (Node2 l1 a t)
      | Up\<^sub>i l2' x' r' \<Rightarrow> T\<^sub>i (Node3 l1 a l2' x' r')
      )
    | Node3 l1 a l2 b l3 \<Rightarrow> (case joinR l3 x r of
        T\<^sub>i t \<Rightarrow> T\<^sub>i (Node3 l1 a l2 b t)
      | Up\<^sub>i l2' x' r' \<Rightarrow> Up\<^sub>i (Node2 l1 a l2) b (Node2 l2' x' r')
    )
    )"

declare joinR.simps[simp del]


lemma inorder_joinR: "\<lbrakk> bal l; bal r; height l \<ge> height r \<rbrakk> \<Longrightarrow> inorder (tree\<^sub>i (joinR l x r)) = inorder l @x # inorder r"
  apply (induction l x r rule: joinR.induct)
  apply (subst joinR.simps)
  apply (fastforce split!: tree23.split up\<^sub>i.split)
  done

lemma bal_joinR: "\<lbrakk> bal l; bal r; height l \<ge> height r \<rbrakk> \<Longrightarrow>
  bal (tree\<^sub>i (joinR l x r)) \<and> height(joinR l x r) = height l"
  sorry



text \<open>\<open>height r\<close> greater\<close>
fun joinL :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i"
where
  "joinL l x r = undefined"

lemma bal_joinL: "\<lbrakk> bal l; bal r; height l \<le> height r \<rbrakk> \<Longrightarrow>
  bal (tree\<^sub>i (joinL l x r)) \<and> height(joinL l x r) = height r"
  text \<open>Note the generalization: We augmented the lemma with a statement about the height of the result.\<close>
  sorry

lemma inorder_joinL: "\<lbrakk> bal l; bal r; height l \<le> height r \<rbrakk> \<Longrightarrow> inorder (tree\<^sub>i (joinL l x r)) = inorder l @x # inorder r"
  sorry


text \<open>Combine both functions\<close>
fun join :: "'a tree23 \<Rightarrow> 'a \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23"
where
"join l x r = undefined"


lemma "\<lbrakk> bal l; bal r \<rbrakk> \<Longrightarrow> bal (join l x r)"
  sorry

lemma "\<lbrakk> bal l; bal r \<rbrakk> \<Longrightarrow> inorder (join l x r) = inorder l @x # inorder r"
  sorry


(*<*)
end
(*>*)
