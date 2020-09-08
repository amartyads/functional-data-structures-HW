theory hw13tmpl
imports Main
begin


fun push :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"push x xs = x # xs"

fun pop :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"pop n xs = drop n xs"

text \<open>You may assume\<close>

definition t_push :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"t_push x xs = 1"

definition t_pop :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
"t_pop n xs = min n (length xs)"

definition \<Phi> :: "'a list \<Rightarrow> int" where
"\<Phi> bs = int(length bs)"

lemma \<Phi>_non_neg: "\<Phi> bs \<ge> 0"
by(simp add: \<Phi>_def)

definition "init = []"

lemma \<Phi>_init: "\<Phi> init = 0"
by(simp add: \<Phi>_def init_def)

lemma push_const: "int(t_push x xs)  + \<Phi>(push x xs) - \<Phi> xs = 2"
apply(induction xs rule: push.induct)
  apply (auto simp add: \<Phi>_def t_push_def)
  done

lemma pop_const: "int(t_pop n xs) + \<Phi>(pop n xs) - \<Phi> xs = 0"
  apply(induction xs rule: pop.induct)
  apply (auto simp add: \<Phi>_def t_pop_def)
  done

end


