theory ex02
  imports Main
begin

datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree" 

fun inorder:: "'a ltree \<Rightarrow> 'a list" where
  "inorder (Leaf x) = [x]"
| "inorder (Node l r) = inorder l @ inorder r"

lemma
  "fold f [] s = s"
  "fold f (x # xs) s = fold f xs (f x s)"
  by auto

fun fold_tree:: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b ltree \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fold_tree f (Leaf b) a = f b a"
| "fold_tree f (Node l r) a = fold_tree f r (fold_tree f l a)"

value "fold_tree
(\<lambda>x y. x + y)
(Node (Leaf (1::nat)) (Node (Leaf 2) (Leaf 4)))
0
"

lemma "fold_tree f t s = fold f (inorder t) s"
  apply(induction t arbitrary: s)
   apply(auto)
  done

fun mirror:: "'a ltree \<Rightarrow> 'a ltree" where
  "mirror (Leaf a) = Leaf a"
| "mirror (Node l r) = Node (mirror r) (mirror l)"

lemma "inorder (mirror t) = rev (inorder t)"
  by (induction t) auto

fun shuffles:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "shuffles [] ys = [ys]"
| "shuffles xs [] = [xs]"
| "shuffles (x#xs) (y#ys) = 
    map(op # x) (shuffles xs (y#ys)) 
    @ map(op # y) (shuffles (x#xs) ys)"

lemma "l\<in>set (shuffles xs ys) \<Longrightarrow> length l = length xs + length ys"
  apply(induction xs ys arbitrary: l rule: shuffles.induct)
    apply(auto)
  done

fun list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0"
| "list_sum (x#xs) = x + list_sum xs"

definition "list_sum' xs = fold (op +) xs 0"

lemma auxi: "fold (op +) xs a = list_sum xs + a"
  apply(induction xs arbitrary: a)
   apply(auto)
  done

lemma "list_sum xs = list_sum' xs"
  unfolding list_sum'_def
  using auxi[where a=0]
  apply auto
  done

end