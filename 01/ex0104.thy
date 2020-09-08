theorem ex0104
  imports Main
begin

term "op#"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] y = [y]"
| "snoc (x # xs) y = x # snoc xs y"

end