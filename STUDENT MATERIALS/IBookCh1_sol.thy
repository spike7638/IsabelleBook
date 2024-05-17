(* this is the "all the stuff written out" version of the Chapter 1 material; 
the filename ends with "_sol", so the theory name has to change as well. And
what I've written here is the end result of the type-this/delete-that instructions,
not a record of every intermediate step.  *)


theory IBookCh1_sol
  imports Main
begin

lemma evens: "\<exists> (n::nat) . 2*n > (k::nat)"
  by presburger

thm evens

lemma junk: "\<exists> (n::nat) p . n > p"
  oops

lemma evens2: "\<exists> (n::nat) . 2*n > (k::nat)"
  using evens by auto

lemma evens3: "\<exists> (n::nat) . 2*n > (k::nat)"
proof -
  have example: "2*(k+1) > k"
    by simp
  show ?thesis using example by blast
qed


lemma evens4: "\<exists> (n::nat) . 2*n > (k::nat)"
proof (cases "k=0")
  case True
  have ex: "2 * 1 > k" using True by simp
  then show ?thesis using ex by blast
next
  case False
  have ex: "2 * k > k" using False by simp (* NB: the prior "ex" is forgotten*) 
  then show ?thesis using ex by blast
qed

lemma evens5: "\<exists> (n::nat) . 2*n > (k::nat)"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then obtain n where nFact: "2*n > k" by blast
  let ?m = "Suc n"
  from nFact have "2 * ?m > Suc k" by auto
  then show ?case by blast
qed

end