theory IbookCh1
  imports Main
begin

lemma "dominate": " 2* (n::nat) + 1 > n + 1"
  by presburger
end