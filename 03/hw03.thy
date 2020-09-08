theory hw03
  imports  "~~/src/HOL/Library/Tree" Main
begin

(* Part 1 - complete*)

declare Let_def [simp]

datatype direction = L|R
type_synonym path = "direction list"

fun valid:: "'a tree \<Rightarrow> path \<Rightarrow> bool" where
  "valid _ [] = True"
| "valid Leaf _ = False"
| "valid (Node ltr a rtr) (x#xs) = (if x = L then (valid ltr xs) else (valid rtr xs))"

fun get:: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree" where
  "get x [] = x"
| "get (Node ltr a rtr) (x# xs) = (if x = L then get ltr xs else get rtr xs)"
| "get _ _ = undefined "

fun put:: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "put x [] y = y"
| "put Leaf _ _ = Leaf"
| "put (Node l a r) (x# xs) y = (if x = L then (Node (put l xs y) a r) else (Node l a (put r xs y)))"

value "put (Node (Node (Leaf) b (Leaf)) d Leaf) [R,R] (Node Leaf q Leaf)"
value "valid (Node Leaf a Leaf) [R]"

lemma put_invalid[simp]: "\<not>valid t p \<Longrightarrow> put t p s = t"
  apply(induction p rule:valid.induct)
     apply(auto)
  done

lemma get_put[simp]: "put t p (get t p) = t"
  apply(induction p rule:get.induct)
     apply(auto)
  done


lemma put_put[simp]: "valid t p \<Longrightarrow> put (put t p s) p s' = put t p s'"
  apply(induction p arbitrary:s' rule: valid.induct)
  apply(auto)
  done

lemma put_get[simp]: "valid t p \<Longrightarrow> get (put t p s) p = s"
  apply(induction t p rule:get.induct)
    apply(auto)
  done
  
lemma valid_put[simp]: "valid t p \<longleftrightarrow> valid (put t p s) p"
  apply(induction t p rule:valid.induct)
    apply(auto)
  done

lemma valid_append[simp]: "valid t (p@q)\<longleftrightarrow> valid t p \<and> valid (get t p) q"
  apply(induction t p rule:valid.induct)
    apply auto
  done

lemma get_append[simp]: "valid t p \<Longrightarrow> get t (p@q) = get (get t p) q"
  apply(induction t p rule:get.induct)
    apply auto
  done

lemma put_append[simp]: "put t (p@q) s = put t p (put (get t p) q s)"
  apply(induction t p rule:get.induct)
  apply auto
  done


(*Part 2 - Incomplete, bst_remdups done, sublist done, first proof done with a generalization which I couldn't prove*)



fun ins :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"ins x Leaf = Node Leaf x Leaf" |
"ins x (Node l a r) =
  (if x < a then Node (ins x l) a r else
   if x > a then Node l a (ins x r)
   else Node l a r)"

fun bst_remdups_aux:: "'a::linorder tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "bst_remdups_aux t [] = inorder t"
| "bst_remdups_aux t (x # xs) = bst_remdups_aux (ins x t) xs"

definition "bst_remdups xs \<equiv> bst_remdups_aux Leaf xs"

value "bst_remdups [1::int,2,3,4,1,5,5,6,6,10,7]"

value "bst_remdups_aux (Node Leaf (7::nat) (Node Leaf (1::nat) Leaf)) [2::nat]"

lemma bst_gen[simp]:"set (bst_remdups_aux t s) = set(bst_remdups_aux t []) \<union> set s"
  sorry

value "filter (\<lambda>x. x \<le> (2::nat)) [2::nat,3,4]"

lemma "set (bst_remdups xs) = set xs"
  unfolding bst_remdups_def
  apply(induction xs)
  apply(auto)
  done

fun remove:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove a [] = []"
| "remove a (x #xs) = (if (a = x) then xs else x #(remove a xs))"

fun sublist:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sublist [] ys = True"
| "sublist xs [] = False"
| "sublist (x#xs) ys = (if x\<in> set ys then sublist xs (remove x ys) else False)"


end