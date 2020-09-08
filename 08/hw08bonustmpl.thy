(*<*)
theory hw08bonustmpl
  imports
    Main
    "HOL-Data_Structures.Tree23_Set"
begin
(*>*)

fun join :: "'a tree23 \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i"
where
  "join Leaf Leaf = T\<^sub>i Leaf"
| "join (Node2 t1 a t2) (Node2 t3 b t4) = (
    case (join t2 t3) of
      T\<^sub>i t23 \<Rightarrow> T\<^sub>i (Node3 t1 a t23 b t4)
    | Up\<^sub>i t2' x t3' \<Rightarrow> Up\<^sub>i (Node2 t1 a t2') x (Node2 t3' b t4)
  )"
| "join (Node2 t1 a t2) (Node3 t3 b t4 c t5) = (
    case (join t2 t3) of
      T\<^sub>i t23 \<Rightarrow> Up\<^sub>i (Node2 t1 a t23) b (Node2 t4 c t5)
    | Up\<^sub>i t2' x t3' \<Rightarrow> Up\<^sub>i (Node2 t1 a t2') x (Node3 t3' b t4 c t5)
)"
| "join (Node3 t1 a t2 b t3) (Node2 t4 c t5) = (
    case (join t3 t4) of
      T\<^sub>i t34 \<Rightarrow> Up\<^sub>i (Node2 t1 a t2) b (Node2 t34 c t5)
    | Up\<^sub>i t3' x t4' \<Rightarrow> Up\<^sub>i (Node2 t1 a t2) b (Node3 t3' x t4' c t5)
)"
| "join (Node3 t1 a t2 b t3) (Node3 t4 c t5 d t6) = (
    case (join t3 t4) of
      T\<^sub>i t34 \<Rightarrow> Up\<^sub>i (Node2 t1 a t2) b (Node3 t34 c t5 d t6)
    | Up\<^sub>i t3' x t4' \<Rightarrow> Up\<^sub>i (Node3 t1 a t2 b t3') x (Node3 t4' c t5 d t6)
)"
| "join _ _ = T\<^sub>i Leaf"


fun del' :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
  "del' x Leaf = T\<^sub>d Leaf"
| "del' x (Node2 Leaf a Leaf) = (if (x = a) then (Up\<^sub>d Leaf) else T\<^sub>d(Node2 Leaf a Leaf))"
| "del' x (Node3 Leaf a Leaf b Leaf) = T\<^sub>d(if x = a then Node2 Leaf b Leaf else
     if x = b then Node2 Leaf a Leaf
     else Node3 Leaf a Leaf b Leaf)"
| "del' x (Node2 l a r) =  (case cmp x a of
     LT \<Rightarrow> node21 (del' x l) a r |
     GT \<Rightarrow> node22 l a (del' x r) |
     EQ \<Rightarrow>  T\<^sub>d(tree\<^sub>i(join l r)))"
|"del' x (Node3 l a m b r) =
  (case cmp x a of
     LT \<Rightarrow> node31 (del' x l) a m b r |
     EQ \<Rightarrow>  T\<^sub>d(Node2 tree\<^sub>i((join (l m)::'a tree23) d r)) |
     GT \<Rightarrow>
       (case cmp x b of
          LT \<Rightarrow> node32 l a (del x m) b r |
          EQ \<Rightarrow> let (b',r') = del_min r in node33 l a m b' r' |
          GT \<Rightarrow> node33 l a m b (del x r)))"


fun del :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>d" where
"del x Leaf = T\<^sub>d Leaf" |
"del x (Node2 Leaf a Leaf) =
  (if x = a then Up\<^sub>d Leaf else T\<^sub>d(Node2 Leaf a Leaf))" |
"del x (Node3 Leaf a Leaf b Leaf) =
  T\<^sub>d(if x = a then Node2 Leaf b Leaf else
     if x = b then Node2 Leaf a Leaf
     else Node3 Leaf a Leaf b Leaf)" |
"del x (Node2 l a r) =
  (case cmp x a of
     LT \<Rightarrow> node21 (del x l) a r |
     GT \<Rightarrow> node22 l a (del x r) |
     EQ \<Rightarrow> let (a',t) = del_min r in node22 l a' t)" |
"del x (Node3 l a m b r) =
  (case cmp x a of
     LT \<Rightarrow> node31 (del x l) a m b r |
     EQ \<Rightarrow> let (a',m') = del_min m in node32 l a' m' b r |
     GT \<Rightarrow>
       (case cmp x b of
          LT \<Rightarrow> node32 l a (del x m) b r |
          EQ \<Rightarrow> let (b',r') = del_min r in node33 l a m b' r' |
          GT \<Rightarrow> node33 l a m b (del x r)))"

(* These are the two essential lemmas needed to instantiate the
  set_by_ordered infrastructure with the new del function:

  (You're not required to repeat the instantiation proof, just these two lemmas are enough. )
*)
lemma inorder_del': "\<lbrakk> bal t ; sorted(inorder t) \<rbrakk> \<Longrightarrow>
  inorder(tree\<^sub>d (del' x t)) = del_list x (inorder t)"
  sorry

lemma bal_tree\<^sub>d_del: "bal t \<Longrightarrow> bal(tree\<^sub>d(del' x t))"
  sorry

text \<open>A few hints:
  \<^item> Prove auxiliary lemmas on \<open>join\<close> that are suitable to discharge your proof obligations, and
    disable simplification of join for your main proof (\<open>declare join.simps[simp del]\<close>).
    This will make proof obligations more readable.
  \<^item> Case splitting by \<open>simp\<close> or \<open>auto\<close> may take quite a long time.
    Use \<open>split!:\<close> instead of \<open>split:\<close> to make it a bit faster.

\<close>


(* In case you are interested how to instantiate the infrastructure with
  the new delete function: *)

definition delete' :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
  "delete' x t = tree\<^sub>d(del' x t)"


interpretation Set_by_Ordered
where empty = Leaf and isin = isin and insert = insert and delete = delete'
and inorder = inorder and inv = bal
proof (standard, goal_cases)
  case 2 thus ?case by(simp add: isin_set)
next
  case 3 thus ?case by(simp add: inorder_insert)
next
  case 4 thus ?case by(simp add: delete'_def inorder_del')
next
  case 6 thus ?case by(simp add: bal_insert)
next
  case 7 thus ?case by(simp add: delete'_def bal_tree\<^sub>d_del)
qed simp+



(*<*)
end
(*>*)
