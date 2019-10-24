(* NOTE:
  This is a temporary file containing the code from `Chi_Calculus/Communication.thy`,
  adapted to include filtering capabilities.
*)
(* TODO:

  - Discuss about possible further generalizations of the filtering versions of the lemmas. See
    the proposed generalizations in the notes accompanying some lemmas.

  - Are `unfiltering_*` versions of the lemmas really necessary? As an example, see the case of
    `unfiltering_unidirectional_bridge_shortcut_redundancy`.

  - Find a more elegant way for the following lemmas to play well with the `equivalence` method:
    `multi_receive_shortcut_redundancy` and `distributor_shortcut_redundancy`.
*)

section \<open>Constructs for Describing Communication\<close>

theory Communication
  imports Chi_Calculus.Core_Bisimilarities "HOL-Library.BNF_Corec"
begin

subsection \<open>Repeated Receiving\<close>

corec multi_receive :: "[chan, val \<Rightarrow> process] \<Rightarrow> process" where
  "multi_receive a P = a \<triangleright> x. (P x \<parallel> multi_receive a P)"
syntax
  "_multi_receive" :: "[chan, pttrn, process] \<Rightarrow> process"
  ("(3_ \<triangleright>\<^sup>\<infinity> _./ _)" [101, 0, 100] 100)
translations
  "a \<triangleright>\<^sup>\<infinity> x. p" \<rightleftharpoons> "CONST multi_receive a (\<lambda>x. p)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax multi_receive} @{syntax_const "_multi_receive"}]
\<close>

(* FIXME:
  We should base the proofs of the compatibility laws on \<open>natural_transition_system\<close>, which would
  have to be extended with support for simulation up to context for that.
*)

lemma basic_multi_receive_preservation:
  assumes "\<And>x. P x \<sim>\<^sub>\<flat> Q x"
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

lemma basic_weak_multi_receive_preservation:
  assumes "\<And>x. P x \<approx>\<^sub>\<flat> Q x"
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

lemma proper_multi_receive_preservation:
  assumes "\<And>x. P x \<sim>\<^sub>\<sharp> Q x"
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<sharp> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

lemma proper_weak_multi_receive_preservation:
  assumes "\<And>x. P x \<approx>\<^sub>\<sharp> Q x"
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<sharp> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

context begin

private lift_definition
  basic_multi_receive :: "[chan, val \<Rightarrow> basic_behavior] \<Rightarrow> basic_behavior"
  is multi_receive
  using basic_multi_receive_preservation .

private lift_definition
  basic_weak_multi_receive :: "[chan, val \<Rightarrow> basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is multi_receive
  using basic_weak_multi_receive_preservation .

private lift_definition
  proper_multi_receive :: "[chan, val \<Rightarrow> proper_behavior] \<Rightarrow> proper_behavior"
  is multi_receive
  using proper_multi_receive_preservation .

private lift_definition
  proper_weak_multi_receive :: "[chan, val \<Rightarrow> proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is multi_receive
  using proper_weak_multi_receive_preservation .

lemmas [equivalence_transfer] =
  basic_multi_receive.abs_eq
  basic_weak_multi_receive.abs_eq
  proper_multi_receive.abs_eq
  proper_weak_multi_receive.abs_eq

end

text \<open>
  We extend \<^theory_text>\<open>natural_simps\<close> with rules for eliminating duplicates of \<open>\<triangleright>\<^sup>\<infinity>\<close>-processes, which are
  based on the observation that \<^const>\<open>multi_receive\<close> is idempotent.

  Incidentally, duplicate removal based on idempotence plays rather well with associativity and
  commutativity rules. The reason is the simplifier's handling of permutative rules, like
  commutativity: these rules are applied only when they lead to a smaller term, where ``smaller'' by
  default means ``lexicographically smaller'' (see Subsection~9.3.3 of the Isabelle/Isar Reference
  Manual). A result of this behavior is that equal processes in a chain of parallel compositions
  will sooner or later stand next to each other. If then a pair of equal processes stands at the end
  of the chain, it can be collapsed by applying an idempotency rule; if it does not stand at the
  end, it can be collapsed by a ``nested'' variant of an idempotency rule, analogous to the
  ``nested'' variant of commutativity.
\<close>
(* FIXME:
  Add a proper reference to the reference manual.
*)

lemma multi_receive_idempotency [natural_simps]:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma multi_receive_nested_idempotency [natural_simps]:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q) \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q"
proof -
  have "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q) \<sim>\<^sub>\<flat> (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x) \<parallel> q"
    using parallel_associativity by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> q"
    using multi_receive_idempotency by equivalence
  finally show ?thesis .
qed

lemma inner_multi_receive_redundancy:
  shows "a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> y. (a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> Q y) \<sim>\<^sub>\<flat> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> b \<triangleright>\<^sup>\<infinity> y. Q y"
  sorry

lemma inner_general_parallel_redundancy:
  assumes "\<And>x Q. P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. (P x \<parallel> Q y) \<sim>\<^sub>\<flat> P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. Q y"
  shows "\<Prod>x\<leftarrow>xs. P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. (\<Prod>x\<leftarrow>xs. P x \<parallel> Q y) \<sim>\<^sub>\<flat> \<Prod>x\<leftarrow>xs. P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. Q y"
proof (induction xs arbitrary: Q)
  case Nil
  show ?case
    unfolding general_parallel.simps(1)
    using natural_simps by equivalence
next
  case (Cons x xs Q)
  have "
    (P x \<parallel> \<Prod>x\<leftarrow>xs. P x) \<parallel> a \<triangleright>\<^sup>\<infinity> y. ((P x \<parallel> \<Prod>x\<leftarrow>xs. P x) \<parallel> Q y)
    \<sim>\<^sub>\<flat>
    P x \<parallel> (\<Prod>x\<leftarrow>xs. P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. (\<Prod>x\<leftarrow>xs. P x \<parallel> (P x \<parallel> Q y)))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> P x \<parallel> (\<Prod>x\<leftarrow>xs. P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. (P x \<parallel> Q y))"
    using Cons.IH by (rule basic_parallel_preservation_right)
  also have "\<dots> \<sim>\<^sub>\<flat> \<Prod>x\<leftarrow>xs. P x \<parallel> (P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. (P x \<parallel> Q y))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> \<Prod>x\<leftarrow>xs. P x \<parallel> (P x \<parallel> a \<triangleright>\<^sup>\<infinity> y. Q y)"
    using assms by (rule basic_parallel_preservation_right)
  also have "\<dots> \<sim>\<^sub>\<flat> (P x \<parallel> \<Prod>x\<leftarrow>xs. P x) \<parallel> a \<triangleright>\<^sup>\<infinity> y. Q y"
    using natural_simps by equivalence
  finally show ?case
    unfolding general_parallel.simps(2) .
qed

subsection \<open>Distributors\<close>

definition distributor :: "[chan, val \<Rightarrow> bool, chan list] \<Rightarrow> process"
  ("(3_ {_}\<Rightarrow> _)" [101, 0, 100] 100) where
  "a {\<phi>}\<Rightarrow> bs = a \<triangleright>\<^sup>\<infinity> x. \<Prod>b\<leftarrow>bs. \<phi> x ? b \<triangleleft> x"

lemma outer_filter_distribution:
  shows "a \<triangleright>\<^sup>\<infinity> x. \<phi> x ? \<Prod>b\<leftarrow>bs. b \<triangleleft> x \<sim>\<^sub>\<flat> a {\<phi>}\<Rightarrow> bs"
proof -
  have "\<phi> x ? \<Prod>b\<leftarrow>bs. b \<triangleleft> x \<sim>\<^sub>\<flat> \<Prod>b\<leftarrow>bs. \<phi> x ? b \<triangleleft> x" for x
  proof (cases "\<phi> x")
    case True
    then have "\<phi> x ? \<Prod>b\<leftarrow>bs. b \<triangleleft> x = \<Prod>b\<leftarrow>bs. b \<triangleleft> x"
      by simp
    also have "\<dots> \<sim>\<^sub>\<flat> \<Prod>b\<leftarrow>bs. \<phi> x ? b \<triangleleft> x"
      using True by simp
    finally show ?thesis .
  next
    case False
    then have "\<phi> x ? \<Prod>b\<leftarrow>bs. b \<triangleleft> x \<sim>\<^sub>\<flat> \<zero>"
      by simp
    also have "\<dots> \<sim>\<^sub>\<flat> \<Prod>b\<leftarrow>bs. \<zero>"
      using natural_simps by (induction bs) (simp_all, equivalence)
    also have "\<dots> \<sim>\<^sub>\<flat> \<Prod>b\<leftarrow>bs. \<phi> x ? b \<triangleleft> x"
      using False by simp
    finally show ?thesis .
  qed
  then show ?thesis
    unfolding distributor_def by (rule basic_multi_receive_preservation)
    (* FIXME: Why doesn't `by equivalence` work? *)
qed

context begin

private lift_definition basic_distributor ::
  "[chan, val \<Rightarrow> bool, chan list] \<Rightarrow> basic_behavior"
  is distributor .

private lift_definition basic_weak_distributor ::
  "[chan, val \<Rightarrow> bool, chan list] \<Rightarrow> basic_weak_behavior"
  is distributor .

private lift_definition proper_distributor ::
  "[chan, val \<Rightarrow> bool, chan list] \<Rightarrow> proper_behavior"
  is distributor .

private lift_definition proper_weak_distributor ::
  "[chan, val \<Rightarrow> bool, chan list] \<Rightarrow> proper_weak_behavior"
  is distributor .

lemmas [equivalence_transfer] =
  basic_distributor.abs_eq
  basic_weak_distributor.abs_eq
  proper_distributor.abs_eq
  proper_weak_distributor.abs_eq

end

(* TODO: Generalize: a {\<phi>}\<Rightarrow> bs \<parallel> a {\<psi>}\<Rightarrow> bs \<sim>\<^sub>\<flat> a {\<phi> \<squnion> \<psi>}\<Rightarrow> bs *)
lemma distributor_idempotency [natural_simps]:
  shows "a {\<phi>}\<Rightarrow> bs \<parallel> a {\<phi>}\<Rightarrow> bs \<sim>\<^sub>\<flat> a {\<phi>}\<Rightarrow> bs"
  unfolding distributor_def using multi_receive_idempotency .

(* TODO: Generalize: a {\<phi>}\<Rightarrow> bs \<parallel> (a {\<phi>}\<Rightarrow> bs \<parallel> p) \<sim>\<^sub>\<flat> a {\<phi> \<squnion> \<psi>}\<Rightarrow> bs \<parallel> p *)
lemma distributor_nested_idempotency [natural_simps]:
  shows "a {\<phi>}\<Rightarrow> bs \<parallel> (a {\<phi>}\<Rightarrow> bs \<parallel> p) \<sim>\<^sub>\<flat> a {\<phi>}\<Rightarrow> bs \<parallel> p"
  unfolding distributor_def using multi_receive_nested_idempotency .

lemma inner_distributor_redundancy:
  shows "a {\<phi>}\<Rightarrow> bs \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a {\<phi>}\<Rightarrow> bs \<parallel> P x) \<sim>\<^sub>\<flat> a {\<phi>}\<Rightarrow> bs \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
  unfolding distributor_def using inner_multi_receive_redundancy .

abbreviation unfiltering_distributor :: "[chan, chan list] \<Rightarrow> process" (infix "\<Rightarrow>" 100) where
  "a \<Rightarrow> bs \<equiv> a {\<top>}\<Rightarrow> bs"

subsection \<open>Loss Servers\<close>

definition loss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>?_" [1000] 1000) where
  "\<currency>\<^sup>?a = a \<Rightarrow> []"

context begin

private lift_definition basic_loss :: "chan \<Rightarrow> basic_behavior"
  is loss .

private lift_definition basic_weak_loss :: "chan \<Rightarrow> basic_weak_behavior"
  is loss .

private lift_definition proper_loss :: "chan \<Rightarrow> proper_behavior"
  is loss .

private lift_definition proper_weak_loss :: "chan \<Rightarrow> proper_weak_behavior"
  is loss .

lemmas [equivalence_transfer] =
  basic_loss.abs_eq
  basic_weak_loss.abs_eq
  proper_loss.abs_eq
  proper_weak_loss.abs_eq

end

lemma loss_idempotency [natural_simps]:
  shows "\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>?a \<sim>\<^sub>\<flat> \<currency>\<^sup>?a"
  unfolding loss_def using distributor_idempotency .

lemma loss_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>?a \<parallel> (\<currency>\<^sup>?a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> p"
  unfolding loss_def using distributor_nested_idempotency .

lemma inner_loss_redundancy:
  shows "\<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>?a \<parallel> P x) \<sim>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  unfolding loss_def using inner_distributor_redundancy .

subsection \<open>Duplication Servers\<close>

definition duplication :: "chan \<Rightarrow> process" ("\<currency>\<^sup>+_" [1000] 1000) where
  "\<currency>\<^sup>+a = a \<Rightarrow> [a, a]"

context begin

private lift_definition basic_duplication :: "chan \<Rightarrow> basic_behavior"
  is duplication .

private lift_definition basic_weak_duplication :: "chan \<Rightarrow> basic_weak_behavior"
  is duplication .

private lift_definition proper_duplication :: "chan \<Rightarrow> proper_behavior"
  is duplication .

private lift_definition proper_weak_duplication :: "chan \<Rightarrow> proper_weak_behavior"
  is duplication .

lemmas [equivalence_transfer] =
  basic_duplication.abs_eq
  basic_weak_duplication.abs_eq
  proper_duplication.abs_eq
  proper_weak_duplication.abs_eq

end

lemma duplication_idempotency [natural_simps]:
  shows "\<currency>\<^sup>+a \<parallel> \<currency>\<^sup>+a \<sim>\<^sub>\<flat> \<currency>\<^sup>+a"
  unfolding duplication_def using distributor_idempotency .

lemma duplication_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>+a \<parallel> (\<currency>\<^sup>+a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> p"
  unfolding duplication_def using distributor_nested_idempotency .

lemma inner_duplication_redundancy:
  shows "\<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> P x) \<sim>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  unfolding duplication_def using inner_distributor_redundancy .

lemma multi_receive_split:
  assumes "\<And>x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>" and "\<And>x. Q x \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<zero>"
  shows "\<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. (P x \<parallel> Q x) \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. Q x"
  sorry

subsection \<open>Duploss Servers\<close>

definition duploss :: "chan \<Rightarrow> process" ("\<currency>\<^sup>*_" [1000] 1000) where
  "\<currency>\<^sup>*a = \<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a"

context begin

private lift_definition basic_duploss :: "chan \<Rightarrow> basic_behavior"
  is duploss .

private lift_definition basic_weak_duploss :: "chan \<Rightarrow> basic_weak_behavior"
  is duploss .

private lift_definition proper_duploss :: "chan \<Rightarrow> proper_behavior"
  is duploss .

private lift_definition proper_weak_duploss :: "chan \<Rightarrow> proper_weak_behavior"
  is duploss .

lemmas [equivalence_transfer] =
  basic_duploss.abs_eq
  basic_weak_duploss.abs_eq
  proper_duploss.abs_eq
  proper_weak_duploss.abs_eq

end

lemma duploss_idempotency [natural_simps]:
  shows "\<currency>\<^sup>*a \<parallel> \<currency>\<^sup>*a \<sim>\<^sub>\<flat> \<currency>\<^sup>*a"
  unfolding duploss_def using natural_simps by equivalence

lemma duploss_nested_idempotency [natural_simps]:
  shows "\<currency>\<^sup>*a \<parallel> (\<currency>\<^sup>*a \<parallel> p) \<sim>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> p"
  unfolding duploss_def using natural_simps by equivalence

lemma inner_duploss_redundancy:
  shows "\<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*a \<parallel> P x) \<sim>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
proof -
  have "(\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a) \<parallel> b \<triangleright>\<^sup>\<infinity> x. ((\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a) \<parallel> P x) \<sim>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> (\<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>?a \<parallel> (\<currency>\<^sup>+a \<parallel> P x)))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> (\<currency>\<^sup>?a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> P x))"
    using inner_loss_redundancy by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> (\<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>+a \<parallel> P x))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> \<currency>\<^sup>?a \<parallel> (\<currency>\<^sup>+a \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x)"
    using inner_duplication_redundancy by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> (\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a) \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
    using natural_simps by equivalence
  finally show ?thesis unfolding duploss_def .
qed

lemma send_idempotency_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a \<triangleleft> x \<parallel> a \<triangleleft> x \<approx>\<^sub>\<flat> \<currency>\<^sup>*a \<parallel> a \<triangleleft> x"
  sorry

subsection \<open>Unidirectional Bridges\<close>

definition unidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> process" ("(3_ {_}\<rightarrow> _)" [101, 0, 100] 100) where
  "a {\<phi>}\<rightarrow> b = a {\<phi>}\<Rightarrow> [b]"

context begin

private lift_definition basic_unidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> basic_behavior"
  is unidirectional_bridge .

private lift_definition basic_weak_unidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> basic_weak_behavior"
  is unidirectional_bridge .

private lift_definition proper_unidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> proper_behavior"
  is unidirectional_bridge .

private lift_definition proper_weak_unidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> proper_weak_behavior"
  is unidirectional_bridge .

lemmas [equivalence_transfer] =
  basic_unidirectional_bridge.abs_eq
  basic_weak_unidirectional_bridge.abs_eq
  proper_unidirectional_bridge.abs_eq
  proper_weak_unidirectional_bridge.abs_eq

end

lemma unidirectional_bridge_idempotency [natural_simps]:
  shows "a {\<phi>}\<rightarrow> b \<parallel> a {\<phi>}\<rightarrow> b \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b"
  unfolding unidirectional_bridge_def using distributor_idempotency .

lemma unidirectional_bridge_nested_idempotency [natural_simps]:
  shows "a {\<phi>}\<rightarrow> b \<parallel> (a {\<phi>}\<rightarrow> b \<parallel> p) \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> p"
  unfolding unidirectional_bridge_def using distributor_nested_idempotency .

lemma inner_unidirectional_bridge_redundancy:
  shows "a {\<phi>}\<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a {\<phi>}\<rightarrow> b \<parallel> P x) \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
  unfolding unidirectional_bridge_def using inner_distributor_redundancy .

lemma multi_receive_shortcut_redundancy:
  assumes "\<theta> = \<phi> \<sqinter> \<psi>"
  shows "a {\<phi>}\<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? P x \<parallel> a \<triangleright>\<^sup>\<infinity> x. \<theta> x ? P x \<approx>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? P x"
  sorry

lemma distributor_shortcut_redundancy:
  assumes "\<theta> = \<phi> \<sqinter> \<psi>"
  shows "a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<Rightarrow> cs \<parallel> a {\<theta>}\<Rightarrow> cs \<approx>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<Rightarrow> cs"
proof -
  have "
    a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<Rightarrow> cs \<parallel> a {\<theta>}\<Rightarrow> cs
    \<approx>\<^sub>\<flat>
    a {\<phi>}\<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x \<parallel> a \<triangleright>\<^sup>\<infinity> x. \<theta> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x"
  proof -
    have "b {\<psi>}\<Rightarrow> cs \<parallel> a {\<theta>}\<Rightarrow> cs \<sim>\<^sub>\<flat> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x \<parallel> a \<triangleright>\<^sup>\<infinity> x. \<theta> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x"
    (* FIXME: Find a nicer proof. *)
      using
        basic.bisimilarity_symmetry_rule and
        basic_parallel_preservation and
        outer_filter_distribution
      by blast
    then show ?thesis
      using
        basic_parallel_preservation_right and
        basic_strong_bisimilarity_in_weak_bisimilarity
      by blast
  qed
  also have "\<dots> \<approx>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x"
    using multi_receive_shortcut_redundancy and assms(1) .
  also have "\<dots> \<approx>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<Rightarrow> cs"
  proof -
    have "a {\<phi>}\<rightarrow> b \<parallel> b \<triangleright>\<^sup>\<infinity> x. \<psi> x ? \<Prod>c\<leftarrow>cs. c \<triangleleft> x \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<Rightarrow> cs"
    (* FIXME: Find a nicer proof. *)
      using outer_filter_distribution
      by (rule basic_parallel_preservation_right)
    then show ?thesis
      using basic_strong_bisimilarity_in_weak_bisimilarity
      by blast
  qed
  finally show ?thesis .
qed

lemma unidirectional_bridge_shortcut_redundancy:
  assumes "\<theta> = \<phi> \<sqinter> \<psi>"
  shows "a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> c \<parallel> a {\<theta>}\<rightarrow> c \<approx>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> c"
  using distributor_shortcut_redundancy and assms(1) unfolding unidirectional_bridge_def .

lemma loop_redundancy_under_duploss:
  shows "\<currency>\<^sup>*a \<parallel> a {\<phi>}\<rightarrow> a \<approx>\<^sub>\<flat> \<currency>\<^sup>*a"
  sorry

lemma sidetrack_redundancy:
  shows "\<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a {\<phi>}\<Rightarrow> (b\<^sub>0 # bs) \<parallel> a {\<phi>}\<rightarrow> b\<^sub>0 \<approx>\<^sub>\<flat> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a {\<phi>}\<Rightarrow> (b\<^sub>0 # bs)"
  sorry

lemma distributor_split:
  shows "\<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> a {\<phi>}\<Rightarrow> bs \<approx>\<^sub>\<flat> \<currency>\<^sup>+a \<parallel> \<Prod>b \<leftarrow> bs. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> bs. a {\<phi>}\<rightarrow> b"
  sorry

abbreviation unfiltering_unidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<rightarrow>" 100) where
  "a \<rightarrow> b \<equiv> a \<Rightarrow> [b]"

(* NOTE: An example of the unfiltering version of a lemma *)
lemma unfiltering_unidirectional_bridge_shortcut_redundancy:
  shows "a \<rightarrow> b \<parallel> b \<rightarrow> c \<parallel> a \<rightarrow> c \<approx>\<^sub>\<flat> a \<rightarrow> b \<parallel> b \<rightarrow> c"
  using unidirectional_bridge_shortcut_redundancy unfolding unidirectional_bridge_def by equivalence

subsection \<open>Bidirectional Bridges\<close>

definition bidirectional_bridge :: "[chan, val \<Rightarrow> bool, val \<Rightarrow> bool, chan] \<Rightarrow> process"
  ("(4_ {_}\<leftrightarrow>{_} _)" [101, 0, 100, 100] 100) where
  "a {\<phi>}\<leftrightarrow>{\<psi>} b = a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> a"

abbreviation backward_unfiltering_bidirectional_bridge :: "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> process"
  ("(3_ {_}\<leftrightarrow> _)" [101, 0, 100] 100) where
  "a {\<phi>}\<leftrightarrow> b \<equiv> a {\<phi>}\<leftrightarrow>{\<top>} b"

abbreviation forward_unfiltering_bidirectional_bridge :: "[chan, val \<Rightarrow> bool, chan] \<Rightarrow> process"
  ("(3_ \<leftrightarrow>{_} _)" [101, 0, 100] 100) where
  "a \<leftrightarrow>{\<phi>} b \<equiv> a {\<top>}\<leftrightarrow>{\<phi>} b"

abbreviation unfiltering_bidirectional_bridge :: "[chan, chan] \<Rightarrow> process" (infix "\<leftrightarrow>" 100) where
  "a \<leftrightarrow> b \<equiv> a {\<top>}\<leftrightarrow>{\<top>} b"

context begin

private lift_definition basic_bidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, val \<Rightarrow> bool, chan] \<Rightarrow> basic_behavior"
  is bidirectional_bridge .

private lift_definition basic_weak_bidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, val \<Rightarrow> bool, chan] \<Rightarrow> basic_weak_behavior"
  is bidirectional_bridge .

private lift_definition proper_bidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, val \<Rightarrow> bool, chan] \<Rightarrow> proper_behavior"
  is bidirectional_bridge .

private lift_definition proper_weak_bidirectional_bridge ::
  "[chan, val \<Rightarrow> bool, val \<Rightarrow> bool, chan] \<Rightarrow> proper_weak_behavior"
  is bidirectional_bridge .

lemmas [equivalence_transfer] =
  basic_bidirectional_bridge.abs_eq
  basic_weak_bidirectional_bridge.abs_eq
  proper_bidirectional_bridge.abs_eq
  proper_weak_bidirectional_bridge.abs_eq

end

lemma bidirectional_bridge_idempotency [natural_simps]:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<phi>}\<leftrightarrow>{\<psi>} b \<sim>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma bidirectional_bridge_nested_idempotency [natural_simps]:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> p) \<sim>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> p"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma inner_bidirectional_bridge_redundancy:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> P x) \<sim>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
proof -
  have "
    (a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> a) \<parallel> c \<triangleright>\<^sup>\<infinity> x. ((a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> a) \<parallel> P x)
    \<sim>\<^sub>\<flat>
    b {\<psi>}\<rightarrow> a \<parallel> (a {\<phi>}\<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (a {\<phi>}\<rightarrow> b \<parallel> (b {\<psi>}\<rightarrow> a \<parallel> P x)))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> b {\<psi>}\<rightarrow> a \<parallel> (a {\<phi>}\<rightarrow> b \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b {\<psi>}\<rightarrow> a \<parallel> P x))"
    using inner_unidirectional_bridge_redundancy by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> (b {\<psi>}\<rightarrow> a \<parallel> c \<triangleright>\<^sup>\<infinity> x. (b {\<psi>}\<rightarrow> a \<parallel> P x))"
    using natural_simps by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> a {\<phi>}\<rightarrow> b \<parallel> (b {\<psi>}\<rightarrow> a \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x)"
    using inner_unidirectional_bridge_redundancy by equivalence
  also have "\<dots> \<sim>\<^sub>\<flat> (a {\<phi>}\<rightarrow> b \<parallel> b {\<psi>}\<rightarrow> a) \<parallel> c \<triangleright>\<^sup>\<infinity> x. P x"
    using natural_simps by equivalence
  finally show ?thesis unfolding bidirectional_bridge_def .
qed

lemma bidirectional_bridge_commutativity [natural_simps]:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<sim>\<^sub>\<flat> b {\<psi>}\<leftrightarrow>{\<phi>} a"
  unfolding bidirectional_bridge_def using parallel_commutativity .

lemma forward_bridge_absorption:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<phi>}\<rightarrow> b \<sim>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma backward_bridge_absorption:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b {\<psi>}\<rightarrow> a \<sim>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b"
  unfolding bidirectional_bridge_def using natural_simps by equivalence

lemma send_channel_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<theta> x ? a \<triangleleft> x \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<theta> x ? b \<triangleleft> x"
  sorry

lemma receive_channel_switch:
  shows "a {\<phi>}\<leftrightarrow> b \<parallel> a \<triangleright> x. P x \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow> b \<parallel> b \<triangleright> x. P x"
  sorry

lemma general_parallel_channel_switch:
  assumes "\<And>x. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> P (fst x) \<approx>\<^sub>\<flat> fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> P (snd x)"
  shows "
    \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. P (fst x)
    \<approx>\<^sub>\<flat>
    \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. P (snd x)"
proof (induction xs)
  case Nil
  show ?case
    unfolding general_parallel.simps(1)
    by equivalence
next
  case (Cons x xs)
  have "
    (fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x) \<parallel> P (fst x) \<parallel> \<Prod>x\<leftarrow>xs. P (fst x)
    \<approx>\<^sub>\<flat>
    (fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> P (fst x)) \<parallel> (\<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. P (fst x))"
    using natural_simps by equivalence
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    (fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> P (snd x)) \<parallel> (\<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. P (snd x))"
    using assms and Cons.IH by (rule basic_weak_parallel_preservation)
  also have "
    \<dots>
    \<approx>\<^sub>\<flat>
    (fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x) \<parallel> (P (snd x) \<parallel> \<Prod>x\<leftarrow>xs. P (snd x))"
    using natural_simps by equivalence
  finally show ?case
    unfolding general_parallel.simps(2) .
qed

lemma multi_receive_channel_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a \<triangleright>\<^sup>\<infinity> x. P x \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b \<triangleright>\<^sup>\<infinity> x. P x"
  sorry

lemma distributor_source_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<theta>}\<Rightarrow> cs \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b {\<theta>}\<Rightarrow> cs"
  unfolding distributor_def using multi_receive_channel_switch .

lemma distributor_target_switch:
  shows "
    \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> a {\<theta>}\<Rightarrow> map fst xs
    \<approx>\<^sub>\<flat>
    \<Prod>x\<leftarrow>xs. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> a {\<theta>}\<Rightarrow> map snd xs" (is "?p \<parallel> _ \<approx>\<^sub>\<flat> ?p \<parallel> _")
proof -
  \<comment> \<open>Specializations of lemmas about~\<open>\<Prod>\<close>:\<close>
  have inner_target_bridges_redundancy: "?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. (?p \<parallel> Q y) \<sim>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. Q y" for Q
    using inner_bidirectional_bridge_redundancy by (rule inner_general_parallel_redundancy)
  have targets_switch: "?p \<parallel> \<Prod>x\<leftarrow>xs. \<theta> y ? fst x \<triangleleft> y \<approx>\<^sub>\<flat> ?p \<parallel> \<Prod>x\<leftarrow>xs.  \<theta> y ? snd x \<triangleleft> y" for y
    using send_channel_switch by (rule general_parallel_channel_switch)
  \<comment> \<open>The actual proof:\<close>
  have "?p \<parallel> a {\<theta>}\<Rightarrow> map fst xs \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. \<Prod>z\<leftarrow>map fst xs. \<theta> y ? z \<triangleleft> y"
    unfolding distributor_def and distributor_def ..
  also have "\<dots> \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. \<Prod>x\<leftarrow>xs. \<theta> y ? fst x \<triangleleft> y"
    unfolding general_parallel_conversion_deferral ..
  also have "\<dots> \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. (?p \<parallel> \<Prod>x\<leftarrow>xs. \<theta> y ? fst x \<triangleleft> y)"
    using inner_target_bridges_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. (?p \<parallel> \<Prod>x\<leftarrow>xs. \<theta> y ? snd x \<triangleleft> y)"
    using targets_switch
    by (blast intro: basic_weak_multi_receive_preservation basic_weak_parallel_preservation_right)
  also have "\<dots> \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. \<Prod>x\<leftarrow>xs. \<theta> y ? snd x \<triangleleft> y"
    using inner_target_bridges_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?p \<parallel> a \<triangleright>\<^sup>\<infinity> y. \<Prod>z\<leftarrow>map snd xs. \<theta> y ? z \<triangleleft> y"
    unfolding general_parallel_conversion_deferral ..
  finally show ?thesis
    unfolding distributor_def and distributor_def .
qed

lemma loss_channel_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>?a \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>?b"
  unfolding distributor_def and loss_def using multi_receive_channel_switch .

lemma duplication_channel_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>+a \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>+b"
proof -
  have "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a \<Rightarrow> [a, a] \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b {\<top>}\<Rightarrow> [a, a]"
    unfolding distributor_def using multi_receive_channel_switch .
  also have "\<dots> \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<zero>) \<parallel> b {\<top>}\<Rightarrow> [a, a]"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<Prod>x\<leftarrow>[(a, b), (a, b)]. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> b {\<top>}\<Rightarrow> map fst [(a, b), (a, b)]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat> \<Prod>x\<leftarrow>[(a, b), (a, b)]. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> b {\<top>}\<Rightarrow> map snd [(a, b), (a, b)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<zero>) \<parallel> b {\<top>}\<Rightarrow> [b, b]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b {\<top>}\<Rightarrow> [b, b]"
    using natural_simps by equivalence
  finally show ?thesis
    unfolding distributor_def and duplication_def .
qed

lemma duploss_channel_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>*a \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>*b"
proof -
  have "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> (\<currency>\<^sup>?a \<parallel> \<currency>\<^sup>+a) \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>?a) \<parallel> \<currency>\<^sup>+a"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>?b) \<parallel> \<currency>\<^sup>+a"
    using loss_channel_switch by (rule basic_weak_parallel_preservation_left)
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>?b \<parallel> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>+a)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<currency>\<^sup>?b \<parallel> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<currency>\<^sup>+b)"
    using duplication_channel_switch by (rule basic_weak_parallel_preservation_right)
  also have "\<dots> \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> (\<currency>\<^sup>?b \<parallel> \<currency>\<^sup>+b)"
    using natural_simps by equivalence
  finally show ?thesis
    unfolding duploss_def .
qed

lemma unidirectional_bridge_source_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> a {\<theta>}\<rightarrow> c \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> b {\<theta>}\<rightarrow> c"
  unfolding unidirectional_bridge_def using distributor_source_switch .

lemma unidirectional_bridge_target_switch:
  shows "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c {\<theta>}\<rightarrow> a \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c {\<theta>}\<rightarrow> b"
proof -
  have "a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c {\<theta>}\<Rightarrow> [a] \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<zero>) \<parallel> c {\<theta>}\<Rightarrow> [a]"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> \<Prod>x\<leftarrow>[(a, b)]. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> c {\<theta>}\<Rightarrow> map fst [(a, b)]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat> \<Prod>x\<leftarrow>[(a, b)]. fst x {\<phi>}\<leftrightarrow>{\<psi>} snd x \<parallel> c {\<theta>}\<Rightarrow> map snd [(a, b)]"
    using distributor_target_switch .
  also have "\<dots> \<approx>\<^sub>\<flat> (a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> \<zero>) \<parallel> c {\<theta>}\<Rightarrow> [b]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat> a {\<phi>}\<leftrightarrow>{\<psi>} b \<parallel> c {\<theta>}\<Rightarrow> [b]"
    using natural_simps by equivalence
  finally show ?thesis
    unfolding unidirectional_bridge_def .
qed

lemma bidirectional_bridge_source_switch:
  shows "a \<leftrightarrow> b \<parallel> a \<leftrightarrow> c \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<leftrightarrow> c"
(*
proof -
  have "a \<leftrightarrow> b \<parallel> (a \<rightarrow> c \<parallel> c \<rightarrow> a) \<approx>\<^sub>\<flat> (a \<leftrightarrow> b \<parallel> a \<rightarrow> c) \<parallel> c \<rightarrow> a"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> (a \<leftrightarrow> b \<parallel> b \<rightarrow> c) \<parallel> c \<rightarrow> a"
    using unidirectional_bridge_source_switch unfolding unidirectional_bridge_def
    by (rule basic_weak_parallel_preservation_left)
  also have "\<dots> \<approx>\<^sub>\<flat> b \<rightarrow> c \<parallel> (a \<leftrightarrow> b \<parallel> c \<rightarrow> a)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> b \<rightarrow> c \<parallel> (a \<leftrightarrow> b \<parallel> c \<rightarrow> b)"
    using unidirectional_bridge_target_switch unfolding unidirectional_bridge_def
    by (rule basic_weak_parallel_preservation_right)
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> (b \<rightarrow> c \<parallel> c \<rightarrow> b)"
    using natural_simps by equivalence
  finally show ?thesis unfolding bidirectional_bridge_def and unidirectional_bridge_def .
qed
*)
  oops (* TODO: Generalize or prove? *)

lemma bidirectional_bridge_target_switch:
  shows "a \<leftrightarrow> b \<parallel> c \<leftrightarrow> a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<leftrightarrow> b"
(*
proof -
  have "a \<leftrightarrow> b \<parallel> c \<leftrightarrow> a \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> a \<leftrightarrow> c"
    using bidirectional_bridge_commutativity by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> b \<leftrightarrow> c"
    using bidirectional_bridge_source_switch .
  also have "\<dots> \<approx>\<^sub>\<flat> a \<leftrightarrow> b \<parallel> c \<leftrightarrow> b"
    using bidirectional_bridge_commutativity by equivalence
  finally show ?thesis .
qed
*)
  oops (* TODO: Generalize or prove? *)

lemma detour_squashing:
  shows "\<nu> b. (a {\<phi>}\<leftrightarrow>{\<psi>} b) \<approx>\<^sub>\<sharp> a {\<phi>}\<rightarrow> a"
  sorry

lemma duploss_detour_collapse:
  shows "\<nu> b. (\<currency>\<^sup>*b \<parallel> a {\<phi>}\<leftrightarrow>{\<psi>} b) \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a"
proof -
  have "\<langle>0\<rangle> \<nu> b. (\<currency>\<^sup>*b \<parallel> a {\<phi>}\<leftrightarrow>{\<psi>} b) \<approx>\<^sub>\<sharp> \<langle>0\<rangle> \<nu> b. (b {\<psi>}\<leftrightarrow>{\<phi>} a \<parallel> \<currency>\<^sup>*b)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<langle>0\<rangle> \<nu> b. (b {\<psi>}\<leftrightarrow>{\<phi>} a \<parallel> \<currency>\<^sup>*a)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      basic_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (meson predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> \<langle>0\<rangle> \<nu> b. (a {\<phi>}\<leftrightarrow>{\<psi>} b)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a \<parallel> a {\<phi>}\<rightarrow> a"
    unfolding tagged_new_channel_def
    using detour_squashing by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>*a"
    using loop_redundancy_under_duploss by equivalence
  finally show ?thesis
    unfolding tagged_new_channel_def .
qed

end
