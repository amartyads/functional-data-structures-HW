(*<*)
theory ex09
  imports Main "HOL-Data_Structures.RBT_Set"
begin
(*>*)


text {* \ExerciseSheet{9}{8.~6.~2018} *}

text \<open>\Exercise{Indicate Unchanged by Option}

  Write an insert function for red-black trees that either inserts the element
  and returns a new tree, or returns None if the element was already in the tree
\<close>

fun ins' :: "'a::linorder \<Rightarrow> 'a rbt \<Rightarrow> 'a rbt option"
(*<*)
where
"ins' x Leaf = Some (R Leaf x Leaf)" |
"ins' x (B l a r) =
  (case cmp x a of
     LT \<Rightarrow> (case ins' x l of None \<Rightarrow> None | Some l \<Rightarrow> Some (baliL l a r)) |
     GT \<Rightarrow> (case ins' x r of None \<Rightarrow> None | Some r \<Rightarrow> Some (baliR l a r)) |
     EQ \<Rightarrow> None)" |
"ins' x (R l a r) =
  (case cmp x a of
    LT \<Rightarrow> (case ins' x l of None \<Rightarrow> None | Some l \<Rightarrow> Some (R l a r)) |
    GT \<Rightarrow> (case ins' x r of None \<Rightarrow> None | Some r \<Rightarrow> Some (R l a r)) |
    EQ \<Rightarrow> None)"

lemma baliR_id: "\<lbrakk>invc l; invc r\<rbrakk> \<Longrightarrow> baliR l a r = B l a r"
  by (cases "(l,a,r)" rule: baliR.cases; auto)

lemma baliL_id: "\<lbrakk>invc l; invc r\<rbrakk> \<Longrightarrow> baliL l a r = B l a r"
  by (cases "(l,a,r)" rule: baliL.cases; auto)
(*>*)

lemma "invc t \<Longrightarrow> case ins' x t of None \<Rightarrow> ins x t = t | Some t' \<Rightarrow> ins x t = t'"
(*<*)
proof (induction x t rule: ins.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x l a r)

  then show ?case
    apply (auto split: option.splits simp: baliL_id baliR_id)
    done

next
  case (3 x l a r)
  then show ?case by (auto split: option.splits)
qed
(*>*)

(*<*)
end
(*>*)
