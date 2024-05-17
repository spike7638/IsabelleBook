(* this is much of the material discussed in the first chapter, although
I've left out the part that you're supposed to type, as well as some 
things I've asked you to type and then delete. If you're trying to 
duplicate what's in the text and it's just not working for some reason, 
you can peek at IBookCh1_sol.thy and perhaps even copy and paste something
from there to try to figure out why it's different from what you typed. 
But DON'T just work through that file...typing this stuff is important
training! *)


theory IBookCh1
  imports Main
begin

lemma evens: "\<exists> (n::nat) . 2*n > (k::nat)"
  sorry

thm evens

(* put the two lines above into a comment 
like this one before proceeding *)

lemma junk: "\<exists> (n::nat) p . n > p"
  oops

lemma evens2: "\<exists> (n::nat) . 2*n > (k::nat)"
  using evens by auto

lemma evens3: "\<exists> (n::nat) . 2*n > (k::nat)"
  oops
lemma evens4: "\<exists> (n::nat) . 2*n > (k::nat)"
  oops
lemma evens5: "\<exists> (n::nat) . 2*n > (k::nat)"
  oops

lemma hw5: "\<forall>(n::nat). n^2 - n + 1 > 0" 
proof -
  fix n::"nat"
  have "n^2 - n + 1 = (n-1)^2 + n" by auto


end