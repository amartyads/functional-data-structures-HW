theory hw02
  imports Main
begin

fun collect:: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b list" where
  "collect x [] = []"
| "collect x ((k,y)#xs) = (if x = k then y # collect x xs else collect x xs)"

definition ctest :: " (int * int) list" where "ctest = [
(2 ,3 ),(2 ,5 ),(2 ,7 ),(2 ,9 ),
(3 ,2 ),(3 ,4 ),(3 ,5 ),(3 ,7 ),(3 ,8 ),
(4 ,3 ),(4 ,5 ),(4 ,7 ),(4 ,9 ),
(5 ,2 ),(5 ,3 ),(5 ,4 ),(5 ,6 ),(5 ,7 ),(5 ,8 ),(5 ,9 ),
(6 ,5 ),(6 ,7 ),
(7 ,2 ),(7 ,3 ),(7 ,4 ),(7 ,5 ),(7 ,6 ),(7 ,8 ),(7 ,9 ),
(8 ,3 ),(8 ,5 ),(8 ,7 ),(8 ,9 ),
(9 ,2 ),(9 ,4 ),(9 ,5 ),(9 ,7 ),(9 ,8 )
]"
value "collect 3 ctest = [2 ,4 ,5 ,7, 8 ]"
value "collect 1 ctest = []"

lemma "collect x ys = map snd (filter (\<lambda>kv. fst kv = x) ys)"
  apply(induction ys)
   apply(auto)
  done

fun collect_tr:: "'b list \<Rightarrow> 'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b list" where
  "collect_tr acc x [] = rev acc"
| "collect_tr acc x ((k,v)#ys) = (if (x = k) then collect_tr (v # acc) x ys else collect_tr acc x ys)"

lemma collect_gen:"collect_tr acc x ys = rev acc @ (collect x ys)"
  apply(induction ys arbitrary:acc)
   apply(auto)
  done

lemma "collect_tr [] x ys = collect x ys"
  apply(induction ys)
   apply(auto simp:collect_gen)
  done






datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree" 

fun lheight:: "'a ltree \<Rightarrow> nat" where
  "lheight (Leaf x) = 0"
| "lheight (Node x y) = max (lheight x) (lheight y) + 1"

value "lheight (Node (Leaf (1::nat)) (Node (Leaf 2) (Leaf 4)))"

fun num_leafs:: "'a ltree \<Rightarrow> nat" where
  "num_leafs (Leaf x) = 1"
| "num_leafs (Node x y) = num_leafs x + num_leafs y"

value "num_leafs (Node (Leaf (1::nat)) (Node (Leaf 2) (Leaf 4)))"

fun balanced:: "'a ltree \<Rightarrow> bool" where
  "balanced (Leaf a) = True"
| "balanced (Node x y) = (op &)((op &)(lheight x = lheight y)(balanced x))(balanced y)"

value "balanced (Node (Node (Leaf a\<^sub>1) (Node (Leaf a\<^sub>1) (Leaf a\<^sub>1))) (Node (Leaf a\<^sub>1) (Node (Leaf a\<^sub>1) (Leaf a\<^sub>1))))"


lemma "balanced t \<Longrightarrow> num_leafs t = 2 ^ lheight t"
  apply(induction t)
  apply(auto)
  done






fun denc :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "denc a [] = []"
| "denc a (x#xs) = (x-a) # denc x xs"

value "denc 0 [1,2,4,8]"
value "denc 0 [3,4,5]"
value "denc 0 [5]"
value "denc 0 []"

fun ddec :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "ddec a [] = []"
| "ddec (a::int) (x#xs) = (x + a) # (ddec (x + a) xs)"

value "ddec 0 [1,1,2,4]"
value "ddec 0 [3,1,1]"
value "ddec 0 [5]"
value "ddec 0 []"

value "ddec 5 (denc 4 [1,2,3])"

lemma encdecgen: "ddec n (denc n l) = l"
  apply(induction l arbitrary:n)
  by auto

lemma "ddec 0 (denc 0 l) = l"
  apply(auto simp:encdecgen)
  done

end