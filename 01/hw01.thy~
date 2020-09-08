theory hw01
  imports Main
begin

fun listsum:: "int list \<Rightarrow> int" where
  "listsum [] = 0"
| "listsum (x # xs) =  listsum xs + x"

value "listsum [1,2,3] = 6"
value "listsum [] = 0"
value "listsum [1,-2,3] = 2"

lemma listsum_filter_x: "listsum (filter (\<lambda>x. x\<noteq>0) l) = listsum l"
  apply(induction l)
  apply(auto)
  done

lemma listsum_append: "listsum (xs @ ys) = listsum xs + listsum ys"
  apply(induction xs)
   apply(auto)
  done

lemma listsum_rev: "listsum (rev xs) = listsum xs"
  apply(induction xs)
   apply(auto simp:listsum_append)
  done

lemma listsum_noneg: "listsum (filter (\<lambda>x. x>0) l) \<ge> listsum l"
  apply(induction l)
   apply(auto)
  done

fun flatten :: "'a list list \<Rightarrow> 'a list" where
  "flatten [] = []"
| "flatten (l#ls) = l @ flatten ls"

value "flatten [[1,2,3],[2]] = [1,2,3,2::int]"
value "flatten [[1,2,3],[],[2]] = [1,2,3,2::int]"

lemma "listsum (flatten xs) = listsum(map listsum xs)"
  apply(induction xs)
  apply(auto simp:listsum_append)
  done

end