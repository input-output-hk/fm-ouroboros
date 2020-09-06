section \<open>
  Equivalence of a Diamond-Shaped Forwarding Praos Network and a Cross-Shaped Broadcasting Praos
  Network
\<close>

theory Ouroboros_Praos_Forwarding_Broadcasting_Equivalence
  imports
    "Chi_Calculus_Examples.Network_Equivalences-Forwarding_Broadcasting"
    Ouroboros_Praos_Implementation
begin

theorem praos_diamond_cross_equivalence:
  assumes "
    (s\<^sub>1, s\<^sub>2, s\<^sub>3, s\<^sub>4) =
      (untyped_channel ts\<^sub>1, untyped_channel ts\<^sub>2, untyped_channel ts\<^sub>3, untyped_channel ts\<^sub>4)"
  and "
    (r\<^sub>1, r\<^sub>2, r\<^sub>3, r\<^sub>4) =
      (untyped_channel tr\<^sub>1, untyped_channel tr\<^sub>2, untyped_channel tr\<^sub>3, untyped_channel tr\<^sub>4)"
  and "
    args = [
      (U\<^sub>1, sk\<^sub>1\<^sub>_\<^sub>v\<^sub>r\<^sub>f, sk\<^sub>1\<^sub>_\<^sub>k\<^sub>e\<^sub>s, sk\<^sub>1\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g, ts\<^sub>1, tr\<^sub>1), (U\<^sub>2, sk\<^sub>2\<^sub>_\<^sub>v\<^sub>r\<^sub>f, sk\<^sub>2\<^sub>_\<^sub>k\<^sub>e\<^sub>s, sk\<^sub>2\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g, ts\<^sub>2, tr\<^sub>2),
      (U\<^sub>3, sk\<^sub>3\<^sub>_\<^sub>v\<^sub>r\<^sub>f, sk\<^sub>3\<^sub>_\<^sub>k\<^sub>e\<^sub>s, sk\<^sub>3\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g, ts\<^sub>3, tr\<^sub>3), (U\<^sub>4, sk\<^sub>4\<^sub>_\<^sub>v\<^sub>r\<^sub>f, sk\<^sub>4\<^sub>_\<^sub>k\<^sub>e\<^sub>s, sk\<^sub>4\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g, ts\<^sub>4, tr\<^sub>4)]"
  and "
    stakeholders =
      \<Prod>(U\<^sub>i, sk\<^sub>i\<^sub>_\<^sub>v\<^sub>r\<^sub>f, sk\<^sub>i\<^sub>_\<^sub>k\<^sub>e\<^sub>s, sk\<^sub>i\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g, ts\<^sub>i, tr\<^sub>i)\<leftarrow>args. stakeholder U\<^sub>i G sk\<^sub>i\<^sub>_\<^sub>v\<^sub>r\<^sub>f sk\<^sub>i\<^sub>_\<^sub>k\<^sub>e\<^sub>s sk\<^sub>i\<^sub>_\<^sub>d\<^sub>s\<^sub>i\<^sub>g (ts\<^sub>i, tr\<^sub>i)"
  shows "
    stakeholders \<parallel>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3
    \<approx>\<^sub>\<sharp>
    stakeholders \<parallel>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
  using diamond_cross_equivalence by equivalence

end
