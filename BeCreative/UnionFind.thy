theory UnionFind
  imports Main
begin

(*Initial definitions*)

definition "init n = [0..<n]"                         (*initial list is a list from 0 to n-1*)
definition "pred ls i = ls!i"                         (*location at every index points to parent*)
definition "is_root ls i \<longleftrightarrow> pred ls i = i"           (*if own parent, then root*)

function (domintros) root_of where                    (*function with custom termination*)
  "root_of ls i = (if is_root ls i then i else root_of ls (ls!i))"
   apply auto[1]
  by blast

thm "root_of.psimps"
thm "root_of.pinduct"


(*A list is a valid UFDS if all its indices are less than the length of the list, and the indices terminate*)
definition "invar ls \<equiv>  \<forall>i<length ls. ls!i < length ls \<and> root_of_dom (ls,i)"  

(*Lemmas*)

(*If an element has itself as a root, it is a root*)
lemma is_root_corr : "ls!i = i \<Longrightarrow> is_root ls i"
  apply(subst is_root_def)
  apply(subst pred_def)
  by simp

(*The init function sets all the members to themselves as roots*)
lemma init_corr : "\<forall>i\<in> set(init n). (is_root (init n) i)"
  apply(subst is_root_def)
  apply(auto)
  by (simp add: pred_def init_def)
  
(*If a member is a root, it is its own root*)
lemma root_of_base: "is_root ls i \<Longrightarrow> root_of ls i = i"
  apply(subst root_of.psimps)
   apply(auto)
  using root_of.domintros by blast

(*The root of a non-root member is the same as the root of its parent's member*)
lemma root_of_step: " \<lbrakk> invar ls; i < length ls; ls!i \<noteq> i \<rbrakk>  \<Longrightarrow> root_of ls i = root_of ls (ls!i)"
  apply(subst root_of.psimps)
  apply (simp add: invar_def)
  by (simp add: pred_def is_root_def)
  
(*The root of a parent is the root of its child*)
lemma root_of_back: " \<lbrakk> invar ls; i < length ls; ls!i \<noteq> i \<rbrakk>  \<Longrightarrow> root_of ls (ls!i) = root_of ls i"
  by (simp add: root_of_step)
  
(*The init function returns a valid UFDS*)
lemma invar_init: "invar (init n)"
  apply(subst init_def)
  apply(subst invar_def)
  apply(auto)
  using is_root_corr root_of.domintros by fastforce

(*union of two sets*)
definition union where "union i j ls = ls[root_of ls i := root_of ls j]"

type_synonym eqcs = "nat \<Rightarrow> nat set"

(*return disjoint set the element belongs to*)
definition \<alpha> :: "nat list \<Rightarrow> eqcs" where "\<alpha> ls i = 
  (if i<length ls then {j. j<length ls \<and> root_of ls j = root_of ls i} else {i})"

(*return if an element is part of a disjoint set after uniting two other elements*)
definition union_eqc :: "nat \<Rightarrow> nat \<Rightarrow> eqcs \<Rightarrow> eqcs"
  where
  "union_eqc x y eqc i = (if i \<in> eqc x \<union> eqc y then eqc x \<union> eqc y else eqc i)"

(*Lemmas*)

(*Every disjoint set from init list has only itself as an element*)
lemma "\<alpha> (init n) i = {i}"
  apply (auto simp add: init_def \<alpha>_def)
  using is_root_corr root_of_base by auto

(*Union does not change length of list*)
lemma length_same : "length ls = length (union a b ls)"
  by (simp add: union_def)






(*Lemmas I couldn't prove*)
lemma length_fixed : "\<lbrakk>invar ls ; x < length ls ; y < length ls ; i < length ls \<rbrakk> \<Longrightarrow> union x y ls ! i < length (union x y ls)"
  apply(simp add: union_def)
  apply(subst root_of.psimps)
   apply(auto)
  using invar_def apply auto[1]
  
  oops

lemma 
  assumes "invar ls" "x<length ls" "y<length ls"
  shows "\<alpha> (union x y ls) = union_eqc x y (\<alpha> ls)"
  oops
  

lemma 
  assumes "invar ls" "x<length ls" "y<length ls"
  shows "invar (union x y ls)"
  unfolding invar_def
proof(intro allI)
  fix i
  have "union x y ls ! i < length (union x y ls)" using assms
    oops

lemma all_have_root: "invar ls \<Longrightarrow> i < length ls \<Longrightarrow> root_of ls i < length ls"
  oops
  

end