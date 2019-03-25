section \<open>Notions of Communication\<close>

theory Communication
  imports Proper_Weak_Transition_System "HOL-Library.BNF_Corec"
begin

corec multi_receive :: "[chan, val \<Rightarrow> process] \<Rightarrow> process" where
  "multi_receive a P = a \<triangleright> x. (P x \<parallel> multi_receive a P)"
syntax
  "_multi_receive" :: "chan \<Rightarrow> pttrn \<Rightarrow> process \<Rightarrow> process"
  ("(3_ \<triangleright>\<^sup>\<infinity> _./ _)" [101, 0, 100] 100)
translations
  "a \<triangleright>\<^sup>\<infinity> x. p" \<rightleftharpoons> "CONST multi_receive a (\<lambda>x. p)"

lemma multi_receive_idempotency: "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

abbreviation loss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>?_" [1000] 1000) where
  "\<currency>\<^sup>?a \<equiv> a \<triangleright>\<^sup>\<infinity> _. \<zero>"

lemma loss_idempotency: "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>?a \<sim>\<^sub>\<flat> \<currency>\<^sup>?a"
  by (fact multi_receive_idempotency)

abbreviation duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>+_" [1000] 1000) where
  "\<currency>\<^sup>+a \<equiv> a \<triangleright>\<^sup>\<infinity> x. (a \<triangleleft> x \<parallel> a \<triangleleft> x)"

lemma duplication_idempotency: "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>+a \<sim>\<^sub>\<flat> \<currency>\<^sup>+a"
  by (fact multi_receive_idempotency)

abbreviation loss_and_duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a \<equiv> \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a"

lemma loss_and_duplication_idempotency: "\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

end