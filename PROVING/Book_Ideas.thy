theory Book_Ideas
  imports Main
begin

(* Three theorems all of which produce the same result *)

consts P ::"nat \<Rightarrow> bool"
lemma T1: "P x" for x
  sorry
lemma T2: "\<And> x. P x"
  sorry
lemma T3: "P x"
  sorry

thm T1 T2 T3
https://isabelle.systems/cookbook/

end