theory IbookCh0
  imports Main
begin

lemma "evens": "\<exists> (n::nat) . 2*n > (k::nat)"
  by presburger

lemma "evens2": "\<exists> (n::nat) . 2*n > (k::nat)"
  using evens by auto

lemma "evens3": "\<exists> (n::nat) . 2*n > (k::nat)"
proof -
  have example: "2 * (k+1) > k"
    by simp
  show ?thesis
    using example by blast
qed

lemma "evens4": "\<exists> (n::nat) . 2*n > (k::nat)"
proof (cases "k = 0") (* Split into cases where this is True or False *)
  case True           (* "True" becomes a synonym for "k = 0" *)
  have ex: " 2 * 1 > k" using True by simp  (* and we use it! *)
  then show ?thesis using ex by blast
next
  case False (* "False" is a synonm for k \<noteq> 0 *)
  have ex: "2 * k > k" using False by auto (* we use it here *)
  then show ?thesis using ex by blast (* and now there are no goals left *)
qed

(* For this proof, we use the idea that every natural number is either zero, 
 * or the successor of some natural number, i.e., an inductive construction 
 * of the naturals. "Suc" is the successor-function built into Isabelle's Main theory.
 *)
lemma "evens5": "\<exists> (n::nat) . 2*n > (k::nat)"
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
