
theory hw10
imports Main
begin

datatype trie = LeafF | LeafT | Node "trie * trie"

fun is_trie :: "nat \<Rightarrow> trie \<Rightarrow> bool"
  where
  "is_trie 0 (Node(x,y)) \<longleftrightarrow> False"
| "is_trie 0 _ \<longleftrightarrow> True"
| "is_trie (Suc n) LeafF \<longleftrightarrow> True"
| "is_trie (Suc n) LeafT \<longleftrightarrow> False"
| "is_trie (Suc n) (Node (x,y)) \<longleftrightarrow> is_trie n x \<and> is_trie n y"

text \<open>Hint: The following should evaluate to true!\<close>
value "is_trie 42 LeafF"
value "is_trie 2 (Node (LeafF,Node (LeafT,LeafF)))"
text \<open>Whereas these should be false\<close>
value "is_trie 42 LeafT" -- \<open>Wrong key length\<close>
value "is_trie 2 (Node (LeafT,Node (LeafT,LeafF)))" -- \<open>Wrong key length\<close>
value "is_trie 1 (Node (LeafT,Node (LeafF,LeafF)))" -- \<open>Superfluous node\<close>

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool"
  where
  "isin (Node (x,y)) [] = False"
| "isin LeafT [] = True"
| "isin LeafF _ = False"
| "isin (Node (x,y)) (b#bx) = (if b then isin y bx else isin x bx)"
| "isin LeafT (b#bx) = False"

value "isin (Node (LeafF,Node (LeafT,LeafF))) [True, False]"
value "isin LeafT []"
value "isin LeafF []"

fun ins :: "bool list \<Rightarrow> trie \<Rightarrow> trie"
  where
  "ins [] _ = LeafT"
| "ins (b#bx) LeafF = (if b then (Node (LeafF, ins bx LeafF)) else (Node ((ins bx LeafF), LeafF)))"
| "ins (b#bx) (Node (x,y)) = (if b then (Node (x, ins bx y)) else (Node ((ins bx x),y)))"
| "ins _ x = x"

value "ins [] LeafF"
value "ins [] LeafT"
value "ins [] (Node(LeafF,LeafT))"
value "ins [True] (Node(LeafF,LeafT))"
value "ins [False] (Node(LeafF,LeafT))"
value "ins [False, False] (Node (LeafF,Node (LeafF,LeafT)))"
value "ins [False] LeafF"
value "ins [True,True,True] (Node (LeafF,Node (LeafT,LeafF)))"


lemma aux1: "\<And>b bx x y bs.
       (\<And>bs n. is_trie n y \<Longrightarrow> length bx = n \<Longrightarrow> isin (ins bx y) bs = (bx = bs \<or> isin y bs)) \<Longrightarrow>
       (\<And>bs n. False \<Longrightarrow> is_trie n x \<Longrightarrow> length bx = n \<Longrightarrow> isin (ins bx x) bs = (bx = bs \<or> isin x bs)) \<Longrightarrow>
       b \<Longrightarrow> isin (Node (x, ins bx y)) bs \<Longrightarrow>
             \<not> isin (Node (x, y)) bs \<Longrightarrow> is_trie (length bx) x \<Longrightarrow> is_trie (length bx) y \<Longrightarrow> True # bx = bs"
 proof -
fix b :: bool and bx :: "bool list" and x :: trie and y :: trie and bsa :: "bool list"
assume a1: "isin (Node (x, ins bx y)) bsa"
assume a2: "\<not> isin (Node (x, y)) bsa"
assume a3: "\<And>bs n. \<lbrakk>is_trie n y; length bx = n\<rbrakk> \<Longrightarrow> isin (ins bx y) bs = (bx = bs \<or> isin y bs)"
assume a4: "is_trie (length bx) y"
have "bsa \<noteq> []"
using a1 by force
then show "True # bx = bsa"
  using a4 a3 a2 a1 by (metis (full_types) isin.simps(4) list.exhaust)
qed



lemma isin_ins1:
  assumes "is_trie n t" and "length as = n"
  shows "isin (ins as t) bs = (as = bs \<or> isin t bs)"
proof -
  show ?thesis using assms
    apply (induction as t arbitrary: bs n rule: ins.induct)
       apply (auto split:if_splits)
    using isin.elims(2) apply blast
    using is_trie.simps(1) isin.elims(2) apply blast
           apply (metis (full_types) is_trie.simps(2) is_trie.simps(4) isin.simps(1) isin.simps(3) isin.simps(4) length_0_conv length_Cons list.exhaust)
    using is_trie.elims(3) apply blast
         apply (smt Suc_length_conv ins.simps(2) is_trie.simps(2) is_trie.simps(4) isin.simps(1) isin.simps(3) isin.simps(4) length_0_conv length_Cons list.exhaust list.inject neq_Nil_conv)
    using is_trie.elims(3) apply blast
    
    using aux1 apply metis
      apply (metis isin.elims(2) isin.simps(4) trie.distinct(5))
     apply (smt isin.elims(2) isin.simps(4) trie.distinct(5))
    by (metis isin.elims(2) isin.simps(4) trie.distinct(5))
qed

lemma isin_ins2:
  assumes "is_trie n t" and "length as = n"
  shows "is_trie n (ins as t)"
proof -
  show ?thesis using assms
   apply (induction as t arbitrary: n rule: ins.induct)
       apply (auto split:if_splits)
    using is_trie.elims(3) apply blast
    using is_trie.elims(3) apply blast
    using is_trie.elims(3) apply blast
    using is_trie.elims(3) by blast
qed

lemma isin_ins:
  assumes "is_trie n t" and "length as = n"
  shows "isin (ins as t) bs = (as = bs \<or> isin t bs)"
    and "is_trie n (ins as t)"
  using assms(1) assms(2) isin_ins1 apply auto[1]
  by (simp add: assms(1) assms(2) isin_ins2)

fun node :: "trie \<times> trie \<Rightarrow> trie" where
  "node (x,y) = (if (x = LeafF \<and> y = LeafF) then LeafF else (Node(x,y)))"


fun delete2 :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
  "delete2 [] _ = LeafF"
| "delete2 (b#bx) LeafF = LeafF"
| "delete2 (b#bx) (Node (x,y)) = (if b then (node (x, delete2 bx y)) else (node ((delete2 bx x),y)))"
| "delete2 _ x = x"

lemma delaux1:
  assumes "is_trie n t" and "length as = n"
  shows "isin (delete2 as t) bs = (as\<noteq>bs \<and> isin t bs)"
proof -
  show ?thesis using assms
   apply (induction as t arbitrary: bs n rule: delete2.induct)
       apply (auto split!:if_splits)
              apply (metis gen_length_code(1) ins.simps(1) is_trie.simps(2) isin.simps(3) isin_ins1 length_code)
             apply (metis isin.elims(2) isin.simps(4) trie.distinct(5))
            apply (metis isin.elims(2) isin.simps(4) trie.distinct(5))
           apply (metis (full_types) isin.simps(1) isin.simps(3) isin.simps(4) list.exhaust)
          apply (smt isin.elims(2) isin.simps(4) trie.simps(7))
         apply (smt isin.elims(2) isin.simps(4) trie.simps(7))
        apply (metis isin.elims(2) isin.simps(4) trie.distinct(5))
       apply (metis isin.elims(2) isin.simps(4) trie.distinct(5))
      apply (metis (full_types) isin.simps(1) isin.simps(3) isin.simps(4) list.exhaust)
     apply (smt isin.elims(2) isin.simps(4) trie.simps(7))
    by (smt isin.elims(2) isin.simps(4) trie.simps(7))
qed

lemma delaux2:
  assumes "is_trie n t"
  shows"(is_trie n (delete2 as t))"
proof -
 show ?thesis using assms
   apply (induction as t arbitrary: n rule: delete2.induct)
      apply (auto split!:if_splits)
   using is_trie.elims(3) apply blast
   using is_trie.elims(3) apply blast
       apply (metis is_trie.simps(1) is_trie.simps(6) old.nat.exhaust)
      apply (metis is_trie.simps(1) is_trie.simps(6) not0_implies_Suc)
     apply (metis is_trie.elims(2) is_trie.simps(4) trie.simps(7))
    apply (metis is_trie.simps(1) is_trie.simps(6) old.nat.exhaust)
   by (metis is_trie.simps(1) is_trie.simps(6) not0_implies_Suc)
qed
  
lemma
  assumes "is_trie n t" and "length as = n"
  shows "isin (delete2 as t) bs = (as\<noteq>bs \<and> isin t bs)"
    and "(is_trie n (delete2 as t))"
  using assms(1) assms(2) delaux1 apply blast
  by (simp add: assms(1) delaux2)

end