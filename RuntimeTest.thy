theory RuntimeTest
  imports VarState PortState ThreadState RuntimeExamples
begin




subsection \<open>Tests on @{term PortState} Operations\<close>

(*  Abdullah: Create passing and failing tests for each of the following operations from Runtime.thy.

fun pdeq :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a PortState"
  where "pdeq (portState::'a PortState) p = update portState p (tl (portState $ p))"

fun phead :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a" 
  where "phead (portState::'a PortState) p = hd (portState $ p)"

fun penq :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a \<Rightarrow> 'a PortState" 
  where "penq (ps::'a PortState) p v = update ps p ((ps $ p) @ [v])"

fun pset :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a UQueue \<Rightarrow> 'a PortState" 
  where "pset (ps::'a PortState) p q = update ps p q"

fun penQ where "penQ (q::'a PortState) P x a b = (\<exists>p. P p \<and> penq q p x a b)"

*)

text \<open>@{term pdeq} success case.\<close>
lemma "pdeq compA_info_initial AOut0Id = map_of [(AOut0Id, []), (AOut1Id, [])]"
  by auto

text \<open>@{term pdeq} success case.\<close>
lemma "pdeq (map_of [(AOut0Id, [0]), (AOut1Id, [])]) AOut0Id 
       = map_of [(AOut0Id, []), (AOut1Id, [])]"
  by auto

text \<open>@{term pdeq} failing case.\<close>
lemma "pdeq (map_of [(AOut0Id, [0]), (AOut1Id, [])]) AOut0Id 
        \<noteq> map_of [(AOut0Id, [0]), (AOut1Id, [])]"
  apply auto
  by (meson list.distinct(1) map_upd_eqD1)

text \<open>@{term pdeq} failing case.\<close>
lemma "pdeq (map_of [(AOut0Id, [0]), (AOut1Id, [0])]) AOut0Id 
        \<noteq> map_of [(AOut0Id, [0]), (AOut1Id, [0])]"
  apply auto
  by (meson list.distinct(1) map_upd_eqD1)

text \<open>@{term phead} success case.\<close>
lemma "phead (map_of [(AOut0Id, [0]), (AOut1Id, [])]) AOut0Id = 0"
  by auto

text \<open>@{term penq} success case.\<close>
lemma "penq compA_info_initial AOut0Id 0 
        = map_of [(AOut0Id, [0]), (AOut1Id, [])]" 
  by auto 

text \<open>@{term penq} failing case.\<close>
lemma "penq compA_info_initial AOut0Id 0 
        \<noteq> map_of [(AOut0Id, []), (AOut1Id, [1])]" 
  apply auto
  using map_upd_eqD1 by fastforce

text \<open>@{term penq} failing case.\<close>
lemma "penq compA_info_initial AOut0Id 0
        \<noteq> map_of [(AOut0Id, [2, 3]), (AOut1Id, [])]" 
  apply auto
  using map_upd_eqD1 by fastforce

text \<open>@{term penq} failing case.\<close>
lemma "penq compA_info_initial AOut0Id 0 
       \<noteq> map_of [(AOut0Id, [0]), (AOut1Id, [1])]" 
  apply auto
  by (metis One_nat_def PortId.inject fun_upd_twist map_upd_eqD1 not_Cons_self2 zero_neq_one)
 

text \<open>@{term pset} success case.\<close>
lemma "pset compA_info_initial AOut0Id [0, 1, 2, 4] 
       = map_of [(AOut0Id, [0, 1, 2, 4]), (AOut1Id, [])]"
  by auto

text \<open>@{term pset} failing case.\<close>
lemma "pset compA_info_initial AOut0Id [0, 1, 2, 4] 
       \<noteq> map_of [(AOut0Id, [1, 2, 3, 4]), (AOut1Id, [])]"
  apply auto
  using map_upd_eqD1 by fastforce
  

text \<open>@{term pset} failing case.\<close>
lemma "pset compA_info_initial AOut0Id [0, 1, 2, 4] 
      \<noteq> map_of [(AOut0Id, []), (AOut1Id, [0, 1, 2, 4])]"
  apply auto
  using map_upd_eqD1 by fastforce

text \<open>@{term pset} failing case.\<close>
lemma "pset compA_info_initial AOut0Id [0, 1, 2, 4] 
      \<noteq> map_of [(AOut0Id, [0, 1, 2, 4]), (AOut1Id, [0, 1, 2, 4])]"
  apply auto
  by (metis PortId.inject Zero_not_Suc fun_upd_other fun_upd_same list.distinct(1) option.inject)

text \<open>@{term pset} failing case.\<close>
lemma "pset compA_info_initial AOut0Id [0, 1, 2, 4]
      \<noteq> map_of [(AOut0Id, []), (AOut1Id, [])]"
  apply auto
  by (meson list.simps(3) map_upd_eqD1)
  
(*
text \<open>@{term penQ} success case.\<close>
lemma "penQ compA_info_initial (mkCSet {AOut0Id}) 0 AOut0Id [0]"
  by (auto simp add: update_def)

lemma "penQ compA_info_initial (mkCSet {AOut0Id}) 0 AOut1Id []"
  by (auto simp add: update_def)

text \<open>@{term penQ} success case.\<close>
lemma "penQ compA_info_initial (mkCSet {AOut0Id, AOut1Id}) 0 AOut0Id [0]"
  by (auto simp add: update_def)

lemma "penQ compA_info_initial (mkCSet {AOut0Id, AOut1Id}) 0 AOut1Id [0]"
  by (auto simp add: update_def)

text "<@{term penQ} failing case.>"
lemma "\<not>(penQ compA_info_initial (mkCSet {AOut0Id}) 0 AOut1Id [0])"
  by (auto simp add: update_def)

text "<@{term penQ} failing case.>"
lemma "\<not>(penQ compA_info_initial (mkCSet {AOut0Id}) 0 AOut0Id [])"
  by (auto simp add: update_def)

text "<@{term penQ} failing case.>"
lemma "\<not>(penQ compA_info_initial (mkCSet {AOut0Id}) 0 AOut1Id [0])"
  by (auto simp add: update_def)

text "<@{term penQ} failing case.> FLAW"
lemma "(penQ compA_info_initial (mkCSet {AOut0Id, AOut1Id}) 0 AOut0Id [])"
  by (auto simp add: update_def)

text "<@{term penQ} failing case.> FLAW"
lemma "(penQ compA_info_initial (mkCSet {AOut0Id, AOut1Id}) 0 AOut0Id [0])"
  by (auto simp add: update_def)

*)

end