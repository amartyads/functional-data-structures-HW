theory hw04
  imports Main  "~~/src/HOL/Library/Tree"
begin

declare Let_def [simp]

datatype 'a rtree = Leaf | Node "'a rtree" nat 'a "'a rtree"

fun num_nodes:: "'a rtree \<Rightarrow> nat" where
  "num_nodes Leaf = 0"
| "num_nodes (Node l n b r) = 1 + num_nodes l + num_nodes r"

fun rbst:: "'a::linorder rtree \<Rightarrow> bool" where
  "rbst Leaf = True"
| "rbst (Node l a b r) = (rbst l \<and> (\<forall>x\<in>set_rtree l. (b > x)) \<and> (\<forall>x\<in>set_rtree r. (b < x)) \<and> (a = num_nodes l) \<and> rbst r)"


value "rbst (Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"

fun rins:: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
  "rins x Leaf = (Node Leaf 0 x Leaf)"
| "rins x (Node l n b r) =
  (if (x < b) then (Node (rins x l) (Suc n) b r) else (Node l n b (rins x r)))"

value "rins (4::nat) (Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"

lemma rins_set[simp]: "set_rtree (rins x t) = insert x (set_rtree t)"
  apply(induction t arbitrary:x)
   apply(auto)
  done


lemma aux1[simp]: "(x\<notin>set_rtree t) \<Longrightarrow> num_nodes (rins x t) = Suc(num_nodes t)"
  apply(induction t arbitrary: x)
   apply(auto)
  done

lemma aux2[simp]: "rbst(Node l a b r) \<Longrightarrow> (num_nodes l = a) "
   apply(auto)
  done

value "rbst  (rtree.Node rtree.Leaf 0 (1::nat) (rtree.Node rtree.Leaf 0 (1::nat) rtree.Leaf))"



lemma "x\<notin>set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> rbst (rins x t)"
  apply(induction t arbitrary: x rule:rbst.induct)
   apply(auto)
  done

fun risin :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> bool" where
  "risin x Leaf = False"
| "risin x (Node l a b r) = 
  (
    if (b < x) then
      (risin x r)
    else if (b > x) then
      (risin x l)
    else
      True
  )"

value "risin (3::nat) (Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"

lemma "rbst t \<Longrightarrow> risin x t \<longleftrightarrow> x\<in>set_rtree t"
  apply(induction t)
   apply(auto)
  done

fun inorder:: "'a rtree \<Rightarrow> 'a list" where
  "inorder Leaf = []"
| "inorder (Node l a b r) = inorder l @ [b] @ inorder r"

fun rank::"'a::linorder \<Rightarrow> _" where
  "rank x Leaf = undefined"
| "rank x (Node l a b r) = (if (x = b) then a else if (x < b) then (rank x l) else (a + 1 + rank x r))"

definition "at_index i l x \<equiv> i<length l \<and> l!i=x"

lemma aux3[simp]:"rbst t \<Longrightarrow> num_nodes t = length (inorder t)"
  apply(induction t)
   apply(auto)
  done


lemma "rbst t \<Longrightarrow> x\<in>set_rtree t \<Longrightarrow> at_index (rank x t) (inorder t) x"
  unfolding at_index_def
  apply(induction t rule:inorder.induct)
   apply(auto)
  sorry

fun select :: "nat \<Rightarrow> 'a::linorder rtree \<Rightarrow> 'a" where
  "select n Leaf = undefined"
| "select n (Node l a b r) = (if (n = a) then b else if n < a then select n l else select (n-a-1) r)"

lemma select_correct: "rbst t \<Longrightarrow> i<length (inorder t) \<Longrightarrow> select i t = inorder t ! i"
  apply(induction i t rule:select.induct)
   apply(auto)
  sorry

end