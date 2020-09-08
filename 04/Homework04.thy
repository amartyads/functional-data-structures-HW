theory Homework04
  imports "BST_Demo"
begin


datatype 'a rtree = Leaf|Node "'a rtree" nat 'a "'a rtree"

fun num_nodes :: "'a rtree \<Rightarrow> nat" where
  "num_nodes Leaf = 0"|
  "num_nodes (Node l a b r) = num_nodes l + num_nodes r + 1"


fun rbst :: "'a::linorder rtree \<Rightarrow> bool" where
  "rbst Leaf = True"|
  "rbst (Node l a b r) = 
    ((rbst l)\<and>
    (\<forall>x\<in>set_rtree l. x<b)\<and>
    (a = num_nodes l)\<and>
    (\<forall>x\<in>set_rtree r. b<x)\<and>
    (rbst r))"
  

value "rbst (Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"
value "set_rtree(Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"

fun rins :: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> 'a rtree" where
  "rins x Leaf = (Node Leaf 0 x Leaf)"|
  "rins x (Node l a b r) = (if x<b then (Node (rins x l) (Suc a) b r) else (Node l a b (rins x r)))"

value "rins 5 (Node (Node Leaf (0::nat) (1::nat) Leaf) (1::nat) 2 (Node Leaf (0::nat) 3 Leaf))"

lemma rins_set[simp]: "set_rtree (rins x t) = insert x (set_rtree t)"
  apply(induction t)
   apply auto
  done

lemma aux1[simp]:  "(x\<notin>set_rtree t) \<Longrightarrow>num_nodes (rins x t) = Suc(num_nodes t)"
  apply(induction t arbitrary:x)
   apply auto
  done

lemma aux[simp]: "rbst(Node l a b r) \<Longrightarrow> (num_nodes l = a) "
  apply auto
  done


lemma "x\<notin>set_rtree t \<Longrightarrow> rbst t \<Longrightarrow> rbst (rins x t)"
  apply(induction t arbitrary: x rule:rbst.induct)
   apply auto
  done

fun risin:: "'a::linorder \<Rightarrow> 'a rtree \<Rightarrow> bool" where
  "risin _ Leaf = False"|
  "risin x (Node l a b r) = ((x=b)\<or>(risin x l)\<or>(risin x r))"

lemma "rbst t \<Longrightarrow> risin x t \<longleftrightarrow> x\<in>set_rtree t"
  apply(induction t)
   apply auto
  done

fun inorder :: "'a rtree \<Rightarrow> 'a list" where
  "inorder Leaf = []"|
  "inorder (Node l a b r) = inorder l @ b # inorder r"

fun rank:: "'a::linorder \<Rightarrow> _" where





end
