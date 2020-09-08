theory ex04self
  imports Main  "~~/src/HOL/Library/Tree"
begin


fun in_range :: "'a::linorder tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "in_range Leaf x y = []"
| "in_range (Node l x r) u v = 
  (if x > u then in_range l u v else [])
@ (if u \<le> x \<and> x \<le> v then [x] else [])
@ (if v > x then in_range r u v else [])"

lemma "bst t \<Longrightarrow> set (in_range t u v) = {x\<in>set_tree t. u\<le>x \<and> x\<le>v}"
  apply (induction t)
  apply auto
  done


text \<open>Show that your list is actually in-order\<close>
lemma "bst t \<Longrightarrow> in_range t u v = filter (\<lambda>x. u\<le>x \<and> x\<le>v) (inorder t)"
  apply (induction t)
  apply simp
  apply (clarsimp)
  apply safe


end
