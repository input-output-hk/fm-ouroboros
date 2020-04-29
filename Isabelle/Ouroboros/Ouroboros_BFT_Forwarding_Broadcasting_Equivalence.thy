section \<open>
  Equivalence of a Diamond-Shaped Forwarding OBFT Network and a Cross-Shaped Broadcasting OBFT
  Network
\<close>

theory Ouroboros_BFT_Forwarding_Broadcasting_Equivalence
  imports
    "Chi_Calculus_Examples.Network_Equivalences-Forwarding_Broadcasting"
    Ouroboros_BFT_Implementation
begin

theorem obft_diamond_cross_equivalence:
  assumes "
    (s\<^sub>1, s\<^sub>2, s\<^sub>3, s\<^sub>4) =
      (untyped_channel ts\<^sub>1, untyped_channel ts\<^sub>2, untyped_channel ts\<^sub>3, untyped_channel ts\<^sub>4)"
  and "
    (r\<^sub>1, r\<^sub>2, r\<^sub>3, r\<^sub>4) =
      (untyped_channel tr\<^sub>1, untyped_channel tr\<^sub>2, untyped_channel tr\<^sub>3, untyped_channel tr\<^sub>4)"
  and "ts = [(ts\<^sub>1, tr\<^sub>1, 1, sk\<^sub>1), (ts\<^sub>2, tr\<^sub>2, 2, sk\<^sub>2), (ts\<^sub>3, tr\<^sub>3, 3, sk\<^sub>3), (ts\<^sub>4, tr\<^sub>4, 4, sk\<^sub>4)]"
  and "servers = \<Prod>(s, r, i, sk)\<leftarrow>ts. server s r G \<Gamma> i sk"
  shows "
    servers \<parallel>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3
    \<approx>\<^sub>\<sharp>
    servers \<parallel>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    cross s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
  using diamond_cross_equivalence by equivalence

end
