(*<*)
theory ex09tmpl
  imports Main "HOL-Data_Structures.RBT_Set"
begin
(*>*)


text {* \ExerciseSheet{9}{8.~6.~2018} *}

text \<open>\Exercise{Indicate Unchanged by Option}

  Write an insert function for red-black trees that either inserts the element
  and returns a new tree, or returns None if the element was already in the tree
\<close>

term map_option

fun ins' :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt option"
where
"ins' x Leaf = Some (R Leaf x Leaf)" |
"ins' x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> (case ins' x l of None \<Rightarrow> None | Some l' \<Rightarrow> Some (baliL l' a r)) |
     GT \<Rightarrow> (case ins' x r of None \<Rightarrow> None | Some r' \<Rightarrow> Some (baliR l a r')) |
     EQ \<Rightarrow> None)" |
"ins' x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> (case ins' x l of None \<Rightarrow> None | Some l' \<Rightarrow> Some (R l' a r)) |
    GT \<Rightarrow> (case ins' x r of None \<Rightarrow> None | Some r' \<Rightarrow> Some (R l a r')) |
    EQ \<Rightarrow> None)"

lemma [simp]: "\<lbrakk>invc r\<rbrakk> \<Longrightarrow> baliR l a r = B l a r"
  by (cases "(l,a,r)" rule: baliR.cases; simp)

lemma [simp]: "\<lbrakk>invc l\<rbrakk> \<Longrightarrow> baliL l a r = B l a r"
  by (cases "(l,a,r)" rule: baliL.cases; simp)

lemma X1: "invc t \<Longrightarrow> case ins' x t of None \<Rightarrow> ins x t = t | Some t' \<Rightarrow> ins x t = t'"
  by (induction x t rule: ins'.induct) (auto split: option.split)

lemma [simp]: "size (baliR l x r) = size l + size r + 1"
  apply (cases "(l,x,r)" rule: baliR.cases) by auto

lemma [simp]: "size (baliL l x r) = size l + size r + 1"
  apply (cases "(l,x,r)" rule: baliL.cases) by auto

lemma X2: "invc t \<Longrightarrow> ins' x t = Some t' \<Longrightarrow> size t < size t'"
  apply (induction x t arbitrary: t' rule: ins'.induct)
  apply (auto split: option.splits if_splits)
  done


lemma "invc t \<Longrightarrow> case ins' x t of None \<Rightarrow> ins x t = t | Some t' \<Rightarrow> ins x t = t' \<and> t\<noteq>t'"
  using X1[of t x] X2[of t x] by (auto split: option.split)


(*<*)
end
(*>*)
