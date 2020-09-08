theory hw12_tmpl
imports
  "HOL-Data_Structures.Base_FDS"
  "HOL-Data_Structures.Tree2"
  "HOL-Library.Multiset"
  Complex_Main
begin



text \<open>
  \Homework{Explicit Priorities}{6.7.2018}

  Modify the priority queue interface to handle multisets of pairs of
  data and priority, i.e., the new \<open>mset\<close> function has the signature
  @{text \<open>mset::'q \<Rightarrow> ('d\<times>'a::linorder) multiset\<close>}.

  Next, implement the new interface using leftist heaps.
  No complexity proofs are required.

  Hints:
    \<^item> Start with the existing theories, and modify them!
    \<^item> Be careful to design a good specification for \<open>get_min\<close>!

\<close>

(** This template provides a copy of the relevant theories, ready for modification. *)


text \<open>Priority queue interface:\<close>

locale Priority_Queue =
fixes empty :: "'q"
and is_empty :: "'q \<Rightarrow> bool"
and insert :: "('d\<times>'a::linorder) \<Rightarrow> 'q \<Rightarrow> 'q"
and get_min :: "'q \<Rightarrow> ('d\<times>'a::linorder)"
and del_min :: "'q \<Rightarrow> 'q"
and invar :: "'q \<Rightarrow> bool"
and mset :: "'q \<Rightarrow> ('d\<times>'a::linorder) multiset"
assumes mset_empty: "mset empty = {#}"
and is_empty: "invar q \<Longrightarrow> is_empty q = (mset q = {#})"
and mset_insert: "invar q \<Longrightarrow> mset (insert x q) = mset q + {#x#}"
and mset_del_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow>
    mset (del_min q) = mset q - {# get_min q #}"
and mset_get_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> get_min q \<in> set_mset(mset q) \<Longrightarrow> \<forall>p \<in> set_mset(mset q). snd (get_min q) \<le> snd p"
and invar_empty: "invar empty"
and invar_insert: "invar q \<Longrightarrow> invar (insert x q)"
and invar_del_min: "invar q \<Longrightarrow> mset q \<noteq> {#} \<Longrightarrow> invar (del_min q)"

text \<open>Extend locale with \<open>merge\<close>. Need to enforce that \<open>'q\<close> is the same in both locales.\<close>

locale Priority_Queue_Merge = Priority_Queue where empty = empty for empty :: 'q +
fixes merge :: "'q \<Rightarrow> 'q \<Rightarrow> 'q"
assumes mset_merge: "\<lbrakk> invar q1; invar q2 \<rbrakk> \<Longrightarrow> mset (merge q1 q2) = mset q1 + mset q2"
and invar_merge: "\<lbrakk> invar q1; invar q2 \<rbrakk> \<Longrightarrow> invar (merge q1 q2)"












fun mset_tree :: "(('d\<times>'a),'b) tree \<Rightarrow> ('d\<times>'a) multiset" where
"mset_tree Leaf = {#}" |
"mset_tree (Node _ l a r) = {#a#} + mset_tree l + mset_tree r"

type_synonym ('d, 'a) lheap = "(('d\<times>'a),nat)tree"

fun rank :: "('d, 'a) lheap \<Rightarrow> nat" where
"rank Leaf = 0" |
"rank (Node _ _ _ r) = rank r + 1"

fun rk :: "('d, 'a) lheap \<Rightarrow> nat" where
"rk Leaf = 0" |
"rk (Node n _ _ _) = n"

text{* The invariants: *}

fun (in linorder) heap :: "(('d\<times>'a),'b) tree \<Rightarrow> bool" where
"heap Leaf = True" |
"heap (Node _ l (d,m) r) =
  (heap l \<and> heap r \<and> (\<forall>(x,y) \<in> set_mset(mset_tree l + mset_tree r). m \<le> y))"

fun ltree :: "('d, 'a) lheap \<Rightarrow> bool" where
"ltree Leaf = True" |
"ltree (Node n l a r) =
 (n = rank r + 1 \<and> rank l \<ge> rank r \<and> ltree l & ltree r)"

definition node :: "('d, 'a) lheap \<Rightarrow> ('d\<times>'a) \<Rightarrow> ('d, 'a) lheap \<Rightarrow> ('d, 'a) lheap" where
"node l a r =
 (let rl = rk l; rr = rk r
  in if rl \<ge> rr then Node (rr+1) l a r else Node (rl+1) r a l)"

fun get_min :: "('d, 'a) lheap \<Rightarrow> ('d\<times>'a::linorder)" where
"get_min(Node n l a r) = a"

text \<open>For function \<open>merge\<close>:\<close>
unbundle pattern_aliases
declare size_prod_measure[measure_function]

fun merge :: "('d, 'a::ord) lheap \<Rightarrow> ('d, 'a) lheap \<Rightarrow> ('d, 'a) lheap" where
"merge Leaf t2 = t2" |
"merge t1 Leaf = t1" |
"merge (Node n1 l1 (d1,a1) r1 =: t1) (Node n2 l2 (d2,a2) r2 =: t2) =
   (if a1 \<le> a2 then node l1 (d1,a1) (merge r1 t2)
    else node l2 (d2,a2) (merge r2 t1))"

lemma merge_code: "merge t1 t2 = (case (t1,t2) of
  (Leaf, _) \<Rightarrow> t2 |
  (_, Leaf) \<Rightarrow> t1 |
  (Node n1 l1 a1 r1, Node n2 l2 a2 r2) \<Rightarrow>
    if snd a1 \<le> snd a2 then node l1 a1 (merge r1 t2) else node l2 a2 (merge r2 t1))"
by(induction t1 t2 rule: merge.induct) (simp_all split: tree.split)

hide_const (open) insert

definition insert :: "('d\<times>'a::ord) \<Rightarrow> ('d, 'a) lheap \<Rightarrow> ('d, 'a) lheap" where
"insert x t = merge (Node 1 Leaf x Leaf) t"

fun del_min :: "('d, 'a::ord) lheap \<Rightarrow> ('d, 'a) lheap" where
"del_min Leaf = Leaf" |
"del_min (Node n l x r) = merge l r"


subsection "Lemmas"

lemma mset_tree_empty: "mset_tree t = {#} \<longleftrightarrow> t = Leaf"
by(cases t) auto

lemma rk_eq_rank[simp]: "ltree t \<Longrightarrow> rk t = rank t"
by(cases t) auto

lemma ltree_node: "ltree (node l a r) \<longleftrightarrow> ltree l \<and> ltree r"
by(auto simp add: node_def)

lemma heap_node: "heap (node l (d,a) r) \<longleftrightarrow>
  heap l \<and> heap r \<and> (\<forall>(x,y) \<in> set_mset(mset_tree l + mset_tree r). a \<le> y)"
by(auto simp add: node_def)


subsection "Functional Correctness"

lemma mset_merge: "mset_tree (merge h1 h2) = mset_tree h1 + mset_tree h2"
by (induction h1 h2 rule: merge.induct) (auto simp add: node_def ac_simps)

lemma mset_insert: "mset_tree (insert x t) = mset_tree t + {#x#}"
by (auto simp add: insert_def mset_merge)

lemma get_min: "\<lbrakk> heap h;  h \<noteq> Leaf \<rbrakk> \<Longrightarrow>  get_min h \<in> set_mset(mset_tree h) \<Longrightarrow> \<forall>(x,y) \<in> set_mset(mset_tree h). snd (get_min h) \<le> y"
  apply(induction h)
   apply auto
   apply blast
  by blast

lemma mset_del_min: "mset_tree (del_min h) = mset_tree h - {# get_min h #}"
by (cases h) (auto simp: mset_merge)

lemma ltree_merge: "\<lbrakk> ltree l; ltree r \<rbrakk> \<Longrightarrow> ltree (merge l r)"
proof(induction l r rule: merge.induct)
  case (3 n1 l1 d1 a1 r1 n2 l2 d2 a2 r2)
  show ?case (is "ltree(merge ?t1 ?t2)")
  proof cases
    assume "a1 \<le> a2"
    hence "ltree (merge ?t1 ?t2) = ltree (node l1 (d1,a1) (merge r1 ?t2))" by simp
    also have "\<dots> = (ltree l1 \<and> ltree(merge r1 ?t2))"
      by(simp add: ltree_node)
    also have "..." using "3.prems" "3.IH"(1)[OF `a1 \<le> a2`] by (simp)
    finally show ?thesis .
  next (* analogous but automatic *)
    assume "\<not> a1 \<le> a2"
    thus ?thesis using 3 by(simp)(auto simp: ltree_node)
  qed
qed simp_all

lemma heap_merge: "\<lbrakk> heap l; heap r \<rbrakk> \<Longrightarrow> heap (merge l r)"
proof(induction l r rule: merge.induct)
  case 3 thus ?case by(auto simp: heap_node mset_merge ball_Un)
qed simp_all

lemma ltree_insert: "ltree t \<Longrightarrow> ltree(insert x t)"
by(simp add: insert_def ltree_merge del: merge.simps split: tree.split)

lemma heap_insert_aux1_aux1[simp]: "heap \<langle>a, \<langle>\<rangle>, x, \<langle>\<rangle>\<rangle>"
  by(induction x)(auto)

lemma heap_insert_aux1[simp]:  "heap t \<Longrightarrow> heap (merge \<langle>a, \<langle>\<rangle>, x, \<langle>\<rangle>\<rangle> t)"
  apply(induction t)
  by(auto simp add:heap_merge)

lemma heap_insert: "heap t \<Longrightarrow> heap(insert x t)"
by(simp add: insert_def heap_merge del: merge.simps split: tree.split)

lemma ltree_del_min: "ltree t \<Longrightarrow> ltree(del_min t)"
by(cases t)(auto simp add: ltree_merge simp del: merge.simps)

lemma heap_del_min: "heap t \<Longrightarrow> heap(del_min t)"
by(cases t)(auto simp add: heap_merge simp del: merge.simps)

text \<open>Last step of functional correctness proof: combine all the above lemmas
to show that leftist heaps satisfy the specification of priority queues with merge.\<close>

interpretation lheap: Priority_Queue_Merge
where empty = Leaf and is_empty = "\<lambda>h. h = Leaf"
and insert = insert and del_min = del_min
and get_min = get_min and merge = merge
and invar = "\<lambda>h. heap h \<and> ltree h" and mset = mset_tree
proof(standard, goal_cases)
  case 1 show ?case by simp
next
  case (2 q) show ?case by (cases q) auto
next
  case 3 show ?case by(rule mset_insert)
next
  case 4 show ?case by(rule mset_del_min)
next
  case 5 thus ?case 
    by (metis (full_types) case_prodE get_min mset_tree.simps(1) prod.sel(2)) 
next
  case 6 thus ?case by(simp)
next
  case 7 thus ?case by(simp add: heap_insert ltree_insert)
next
  case 8 thus ?case by(simp add: heap_del_min ltree_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: heap_merge ltree_merge)
qed






end
