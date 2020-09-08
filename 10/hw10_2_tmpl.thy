(*<*)
theory hw10_2_tmpl
imports Trie1 "HOL-Library.List_lexord"
begin
(*>*)
(* Incomplete *)

fun path_trav :: "trie \<Rightarrow> bool list \<Rightarrow> bool list list" where
  "path_trav Leaf bs = []"
| "path_trav (Node b (x,y)) bs = (if b then ([bs] @ (path_trav x (bs@[True])) @ (path_trav y (bs@[False])))
                                    else ( (path_trav x (bs@[True])) @ (path_trav y (bs@[False]))))"

fun enum :: "trie \<Rightarrow> bool list list"
  where
    "enum Leaf = []"
  | "enum t = path_trav t []"

value "enum (Node False ((Node True (Leaf, Leaf)),Leaf))"
value "path_trav (Node False ((Node True (Leaf, Leaf)),Leaf)) []"

lemma enum_correct1: "set (enum t) = { xs. isin t xs }"
proof(induction rule: isin.induct)
  case (1 ks)
then show ?case by auto
next
case (2 b l r ks)
  then show ?case 
qed
  
  oops
  
lemma enum_correct2: "sorted_wrt op< (enum t)"
  
    oops

lemma enum_correct:
    "set (enum t) = { xs. isin t xs }" and "sorted_wrt op< (enum t)"
    oops



text \<open>
  Note that Booleans are ordered by \<open>False < True\<close>, and
  that we imported @{theory "List_lexord"}, which defines
  a lexicographic ordering on lists, if the elements are ordered.
\<close>

value "[True,True,False] < [True,True,True,True]"



(*<*)
end
(*>*)
