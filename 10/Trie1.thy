(* Author: Tobias Nipkow *)

section "Trie1"

theory Trie1
imports Main
begin

lemma [simp]: "(\<forall>x. x \<noteq> y) = False"
by blast

hide_const (open) insert

declare Let_def[simp]


subsection "Trie"

datatype trie = Leaf | Node bool "trie * trie"

fun isin :: "trie \<Rightarrow> bool list \<Rightarrow> bool" where
"isin Leaf ks = False" |
"isin (Node b (l,r)) ks =
   (case ks of
      [] \<Rightarrow> b |
      k#ks \<Rightarrow> isin (if k then r else l) ks)"

fun insert :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"insert [] Leaf = Node True (Leaf,Leaf)" |
"insert [] (Node b lr) = Node True lr" |
"insert (k#ks) Leaf =
  Node False (if k then (Leaf, insert ks Leaf)
                   else (insert ks Leaf, Leaf))" |
"insert (k#ks) (Node b (l,r)) =
  Node b (if k then (l, insert ks r)
               else (insert ks l, r))"

lemma isin_insert: "isin (insert as t) bs = (as = bs \<or> isin t bs)"
apply(induction as t arbitrary: bs rule: insert.induct)
apply (auto split: list.splits)
done

text \<open>A simple implementation of delete; does not shrink the trie!\<close>

fun delete :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"delete ks Leaf = Leaf" |
"delete ks (Node b (l,r)) =
   (case ks of
      [] \<Rightarrow> Node False (l,r) |
      k#ks' \<Rightarrow> Node b (if k then (l, delete ks' r) else (delete ks' l, r)))"

lemma "isin (delete as t) bs = (as \<noteq> bs \<and> isin t bs)"
apply(induction as t arbitrary: bs rule: delete.induct)
apply (auto split: list.splits)
done

fun node :: "bool \<Rightarrow> trie * trie \<Rightarrow> trie" where
"node b lr = (if \<not> b \<and> lr = (Leaf,Leaf) then Leaf else Node b lr)"

fun delete2 :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"delete2 ks Leaf = Leaf" |
"delete2 ks (Node b (l,r)) =
   (case ks of
      [] \<Rightarrow> node False (l,r) |
      k#ks' \<Rightarrow> node b (if k then (l, delete2 ks' r) else (delete2 ks' l, r)))"

lemma "isin (delete2 as t) bs = isin (delete as t) bs"
apply(induction as t arbitrary: bs rule: delete2.induct)
 apply simp
apply (force split: list.splits)
done


subsection "Patricia Trie"

datatype ptrie = LeafP | NodeP "bool list" bool "ptrie * ptrie"

fun isinP :: "ptrie \<Rightarrow> bool list \<Rightarrow> bool" where
"isinP LeafP ks = False" |
"isinP (NodeP ps b (l,r)) ks =
  (let n = length ps in
   if ps = take n ks
   then case drop n ks of [] \<Rightarrow> b | k#ks' \<Rightarrow> isinP (if k then r else l) ks'
   else False)"

fun split where
"split [] ys = ([],[],ys)" |
"split xs [] = ([],xs,[])" |
"split (x#xs) (y#ys) =
  (if x\<noteq>y then ([],x#xs,y#ys)
   else let (ps,xs',ys') = split xs ys in (x#ps,xs',ys'))"

fun insertP :: "bool list \<Rightarrow> ptrie \<Rightarrow> ptrie" where
"insertP ks LeafP  = NodeP ks True (LeafP,LeafP)" |
"insertP ks (NodeP ps b (l,r)) =
  (case split ks ps of
     (qs,k#ks',p#ps') \<Rightarrow>
       let tp = NodeP ps' b (l,r); tk = NodeP ks' True (LeafP,LeafP) in
       NodeP qs False (if k then (tp,tk) else (tk,tp)) |
     (qs,k#ks',[]) \<Rightarrow>
       NodeP ps b (if k then (l, insertP ks' r) else (insertP ks' l, r)) |
     (qs,[],p#ps') \<Rightarrow>
       let t = NodeP ps' b (l,r) in
       NodeP qs True (if p then (LeafP,t) else (t,LeafP)) |
     (qs,[],[]) \<Rightarrow> NodeP ps True (l,r))"

fun prefix_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie" where
"prefix_trie [] t = t" |
"prefix_trie (k#ks) t =
  (let t' = prefix_trie ks t in Node False (if k then (Leaf,t') else (t',Leaf)))"

fun abs_ptrie :: "ptrie \<Rightarrow> trie" where
"abs_ptrie LeafP = Leaf" |
"abs_ptrie (NodeP ps b (l,r)) = prefix_trie ps (Node b (abs_ptrie l, abs_ptrie r))"

lemma isin_prefix_trie: "isin (prefix_trie ps t) ks =
 (length ks \<ge> length ps \<and>
  (let n = length ps in ps = take n ks \<and> isin t (drop n ks)))"
apply(induction ps arbitrary: ks)
apply(auto split: list.split)
done

lemma isinP: "isinP t ks = isin (abs_ptrie t) ks"
apply(induction t arbitrary: ks rule: abs_ptrie.induct)
 apply(auto simp: isin_prefix_trie split: list.split)
 using nat_le_linear apply force
using nat_le_linear apply force
done

lemma prefix_trie_Leafs: "prefix_trie ks (Node True (Leaf,Leaf)) = insert ks Leaf"
apply(induction ks)
apply auto
done

lemma insert_prefix_trie_same:
  "insert ps (prefix_trie ps (Node b lr)) = prefix_trie ps (Node True lr)"
apply(induction ps)
apply auto
done

lemma insert_append: "insert (ks @ k # ks') (prefix_trie ks (Node b (t1,t2))) =
  prefix_trie ks (Node b (if k then (t1, insert ks' t2) else (insert ks' t1, t2)))"
apply(induction ks)
apply auto
done

lemma prefix_trie_append: "prefix_trie (ps @ qs) t = prefix_trie ps (prefix_trie qs t)"
apply(induction ps)
apply auto
done

lemma split_if: "split ks ps = (qs, ks', ps') \<Longrightarrow>
  ks = qs @ ks' \<and> ps = qs @ ps' \<and> (ks' \<noteq> [] \<and> ps' \<noteq> [] \<longrightarrow> hd ks' \<noteq> hd ps')"
apply(induction ks ps arbitrary: qs ks' ps' rule: split.induct)
apply(auto split: prod.splits if_splits)
done

lemma abs_ptrie_insertP:
  "abs_ptrie (insertP ks t) = insert ks (abs_ptrie t)"
apply(induction t arbitrary: ks)
apply(auto simp: prefix_trie_Leafs insert_prefix_trie_same insert_append prefix_trie_append
           dest!: split_if split: list.split prod.split)
done

corollary isinP_insertP: "isinP (insertP ks t) ks' = (ks=ks' \<or> isinP t ks')"
by (simp add: isin_insert isinP abs_ptrie_insertP)

end
