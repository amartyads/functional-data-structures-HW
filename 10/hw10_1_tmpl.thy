(*<*)
theory hw10_1_tmpl
imports Main
begin
(*>*)


text \<open>\NumHomework{Tries with Same-Length Keys}{22.~6.~2018}

  Consider the following trie datatype:
\<close>

datatype trie = LeafF | LeafT | Node "trie * trie"

text \<open>It is meant to store keys of the same length only.
  Thus, the @{const Node} constructor stores inner nodes, and there are two
  types of leaves, @{const LeafF} if this path is not in the set,
  and @{const LeafT} if it is in the set.

  Define an invariant \<open>is_trie N t\<close> that states that all keys in \<open>t\<close>
  have length \<open>N\<close>, and that there are no superfluous nodes, i.e.,
  no nodes of the form @{term \<open>Node (LeafF, LeafF)\<close>}.
\<close>

fun is_trie :: "nat \<Rightarrow> trie \<Rightarrow> bool"
where
  "is_trie 0 (Node (x,y)) \<longleftrightarrow> False"
| "is_trie 0 _ \<longleftrightarrow> True"
| "is_trie _ (Node (LeafF, LeafF)) \<longleftrightarrow> False"
| "is_trie (Suc n) LeafT \<longleftrightarrow> False"
| "is_trie (Suc n) LeafF \<longleftrightarrow> True"
(*| "is_trie (Suc 0) (Node (x,y)) \<longleftrightarrow> ((x = LeafF) \<or> (x = LeafT)) \<and> ((y = LeafF) \<or> (y = LeafT))"*)
| "is_trie (Suc n) (Node (x,y)) \<longleftrightarrow> is_trie n x \<and> is_trie n y"

text \<open>Hint: The following should evaluate to true!\<close>
value "is_trie 42 LeafF"
value "is_trie 2 (Node (LeafF,Node (LeafT,LeafF)))"
text \<open>Whereas these should be false\<close>
value "is_trie 42 LeafT" -- \<open>Wrong key length\<close>
value "is_trie 2 (Node (LeafT,Node (LeafT,LeafF)))" -- \<open>Wrong key length\<close>
value "is_trie 1 (Node (LeafT,Node (LeafF,LeafF)))" -- \<open>Superfluous node\<close>

value "is_trie 1 (Node (LeafT,LeafF))"


text \<open>Define membership, insert, and delete functions, and prove them correct! \<close>

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool"
  where
  "isin (Node (x, y)) (b#[]) = (if b then (x = LeafT) else (y = LeafT))"
| "isin (Node (x, y)) (b#bs) = (if b then (isin x bs) else (isin y bs))"
| "isin LeafT [] = True"
| "isin _ _ = False"

value "isin (Node (LeafF,Node (LeafT,LeafF))) [False, True]"

fun ins :: "bool list \<Rightarrow> trie \<Rightarrow> trie"
  where
  "ins (b#[]) LeafF = (if b then (Node (LeafT, LeafF)) else (Node(LeafF, LeafT)))"
| "ins (b#[]) LeafT = (if b then (Node (LeafT, LeafF)) else (Node(LeafF, LeafT)))"
| "ins (b#[]) (Node(x,y)) = (if b then (Node (LeafT, y)) else (Node(x, LeafT)))"
| "ins [] x = x"
| "ins (b#bs) (Node(x,y)) =  (if b then (Node ((ins bs x),y)) else (Node (x, (ins bs y))))"
| "ins (b#bs) LeafF = (if b then (Node ((ins bs LeafF),LeafF)) else (Node (LeafF, (ins bs LeafF))))"
| "ins (b#bs) LeafT = (if b then (Node ((ins bs LeafT),LeafF)) else (Node (LeafF, (ins bs LeafT))))"

(*fun ins :: "bool list \<Rightarrow> trie \<Rightarrow> trie"
  where
  "ins [] x = LeafT"
| "ins (b#bs) (Node(x,y)) =  (if b then (Node ((ins bs x),y)) else (Node (x, (ins bs y))))"
| "ins (b#bs) x = (if b then (Node ((ins bs x),LeafF)) else (Node (LeafF, (ins bs x))))"*)

value "ins [True, False] (Node (LeafF,Node (LeafT,LeafF)))"
value "ins [False] LeafF"
value "ins [True,True,True] (Node (LeafF,Node (LeafT,LeafF)))"



lemma isin_ins1:
  assumes "is_trie n t" and "length as = n"
  shows "isin (ins as t) bs = (as = bs \<or> isin t bs)"
  apply (induction as t arbitrary: bs n rule: ins.induct)
  
  
  
  
  


lemma isin_ins2:
  assumes "is_trie n t" and "length as = n"
  shows "is_trie n (ins as t)"
proof(induction as)
  case Nil
then show ?case
  by (simp add: assms(1))
next
case (Cons a as)
  then show ?case
    by (metis One_nat_def ins.simps(2) ins.simps(3) is_trie.simps(2) isin.simps(4) isin_ins1 le_numeral_extra(4) length_Cons list.size(3) not_less_eq_eq not_one_le_zero order_antisym_conv zero_induct)
qed




lemma isin_ins:
  assumes "is_trie n t" and "length as = n"
  shows "isin (ins as t) bs = (as = bs \<or> isin t bs)"
    and "is_trie n (ins as t)"
  using assms(1) assms(2) isin_ins1 apply auto[1]


fun delete2 :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
  "delete2 _ _ = undefined"

lemma
  assumes "is_trie n t"
  shows "isin (delete2 as t) bs = (as\<noteq>bs \<and> isin t bs)"
    and "(is_trie n (delete2 as t))"
  oops

text \<open>Hints:
  \<^item> Like in the \<open>delete2\<close> function for standard tries, you may want to define
    a "smart-constructor" \<open>node :: trie \<times> trie \<Rightarrow> trie\<close> for nodes,
    that constructs a node and handles the case that both successors are \<open>LeafF\<close>.
  \<^item> Consider proving auxiliary lemmas about the smart-constructor, instead of
    always unfolding it with the simplifier.
\<close>



(*<*)
end
(*>*)
