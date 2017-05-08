(**)

theory KMP
  imports "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin
  
  term "SPEC (\<lambda>x::nat. x \<in> {4,7,9})"
  
section\<open>Definition "substring"\<close>
  definition "is_substring_at' t s i \<equiv> take (length s) (drop i t) = s"  
  
  text\<open>Problem:\<close>
  value "is_substring_at' [5] [] 5"
  value "is_substring_at' [5] [5] 5"
  value "is_substring_at' [] [] 3"
  
  text\<open>For the moment, we use this instead:\<close>
  fun is_substring_at where
    "is_substring_at (t#ts) (s#ss) 0 \<longleftrightarrow> t=s \<and> is_substring_at ts ss 0" |
    "is_substring_at (t#ts) ss (Suc i) \<longleftrightarrow> is_substring_at ts ss i" |
    "is_substring_at t [] 0 \<longleftrightarrow> True" |
    "is_substring_at [] _ _ \<longleftrightarrow> False"
  
  value "is_substring_at [5] [] 5"
  value "is_substring_at [5] [5] 5"
  value "is_substring_at [] [] 3"
  text\<open>Better, I suppose?\<close>
        
  lemma "i \<le> length t \<Longrightarrow> is_substring_at t s i \<longleftrightarrow> is_substring_at' t s i"
    unfolding is_substring_at'_def
    by (induction t s i rule: is_substring_at.induct) auto
      
  (*Todo: third alternative: inductive is_substring_at*)

section\<open>Naive algorithm\<close>
    
subsection\<open>Invariants\<close>
  definition "I_out_na t s \<equiv> \<lambda>(i,j(*_?*),found).
    \<not>found \<and> j = 0 \<and> (\<forall>i' < i. \<not>is_substring_at t s i')
    \<or> found \<and> is_substring_at t s i"  
  definition "I_in_na t s iout (*KMP should need jout, too*) \<equiv> \<lambda>(j,found).
    \<not>found \<and> j < length s \<and> (\<forall>j' < j. t!(iout+j') = s!(j'))
    \<or> found \<and> j = length s \<and> is_substring_at t s iout"

subsection\<open>Algorithm\<close>
  definition "na t s \<equiv> do {
    let i=0;
    let j=0;
    (_,_,found) \<leftarrow> WHILEI (I_out_na t s) (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_in_na t s i) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + 1;
        let j = 0;
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"

lemma all_positions_step:
  "\<lbrakk>\<forall>j'<aba. t ! (ab + j') = s ! j'; t ! (ab + aba) = s ! aba\<rbrakk>
       \<Longrightarrow> \<forall>j'\<le>aba. t ! (ab + j') = s ! j'"
  using le_neq_implies_less by blast
  
lemma substring_step:
  "\<lbrakk>length s + i < length t; is_substring_at t s i; t ! (i + length s) = x\<rbrakk> \<Longrightarrow> is_substring_at t (s@[x]) i"
  apply (induction t s i rule: is_substring_at.induct)
  apply auto
  using is_substring_at.elims(3) by fastforce

lemma empty_substring: "i \<le> length t
         \<Longrightarrow> is_substring_at t [] i"
  apply (induction t arbitrary: i)
  apply auto
  using is_substring_at.elims(3) by force

lemma all_positions_substring:
  "\<lbrakk>length s \<le> length t;
    i \<le> length t - length s;
    \<forall>j'<length s. t ! (i + j') = s ! j'\<rbrakk>
       \<Longrightarrow> is_substring_at t s i"
  proof (induction s arbitrary: t i rule: rev_induct)
    case Nil
    then show ?case by (simp add: empty_substring)
  next
    case (snoc x xs)
    moreover from `length (xs @ [x]) \<le> length t` have "length xs \<le> length t" by simp
    moreover have "i \<le> length t - length xs"
      using snoc.prems(2) by auto
    moreover have "\<forall>j'<length xs. t ! (i + j') = xs ! j'"
      by (metis le_refl length_append less_le_trans nth_append snoc.prems(3) trans_le_add1)
    ultimately have f: "is_substring_at t xs i"
      using snoc.IH by blast
    show ?case
      apply (rule substring_step)
      using snoc.prems(1) snoc.prems(2) apply auto[1]
      apply (fact f)
      by (simp add: snoc.prems(3))
  qed

lemma "\<lbrakk>s \<noteq> []; t \<noteq> []; length s \<le> length t\<rbrakk>
  \<Longrightarrow> na t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding na_def I_out_na_def I_in_na_def
    (*are these safe?*)apply refine_vcg apply vc_solve
    apply (metis all_positions_substring less_SucE)
    using less_antisym apply blast
    oops

(*ToDo: WHILET statt WHILE*)
text\<open>Zusätzliche Voraussetzungen nötig! Auch Seidl sagen?\<close>
      
section\<open>Knuth–Morris–Pratt algorithm\<close>
subsection\<open>Auxiliary definitions\<close>
  definition border :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where "border s j \<equiv> undefined"
  
  (*Todo: Properties*)
  thm longest_common_prefix

subsection\<open>Invariants\<close>
  definition "I_outer \<equiv> \<lambda>(i,j,found). undefined"  
  definition "I_inner iout jout \<equiv> \<lambda>(j,found). undefined"  

subsection\<open>Algorithm\<close>
  definition "kmp t s \<equiv> do {
    let i=0; let j=0;

    (_,_,found) \<leftarrow> WHILEI I_outer (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_inner i j) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + (j + 1 - border s j);
        let j = max 0 (border s j - 1); (*max not necessary*)
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"
      
    
    
  lemma "kmp t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding kmp_def
    apply refine_vcg  
    apply vc_solve
    oops
      
section\<open>Notes and Tests\<close>

  term "\<lambda>t s. SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at t s i | Some i \<Rightarrow> is_substring_at t s i \<and> (\<forall>j. is_substring_at t s j \<longrightarrow> i\<le>j))"
  
  
  term "RETURN (4::nat) = SPEC (\<lambda>x. x=4)" 
  
  definition "test \<equiv> do {
    x \<leftarrow> SPEC (\<lambda>x::nat. x<5);
    y \<leftarrow> SPEC (\<lambda>y. y<10);
    RETURN (x+y)
  }"  
  
  lemma "test \<le> SPEC (\<lambda>x. x<14)"
    unfolding test_def
    apply refine_vcg by auto  
  
  definition "i_test2 x\<^sub>0 \<equiv> \<lambda>(x,s). x\<ge>0 \<and> x\<^sub>0*5 = x*5+s"
  
  definition "test2 x\<^sub>0 \<equiv> do {
    (_,s) \<leftarrow> WHILEIT (i_test2 x\<^sub>0) (\<lambda>(x,s). x>0) (\<lambda>(x,s). do {
      let s = s + 5;
      let x = x - 1;
      RETURN (x,s)
    }) (x\<^sub>0::int,0::int);
    RETURN s
  }"  
  
  term "measure (nat o fst)"
    
  lemma "x\<ge>0 \<Longrightarrow> test2 x \<le> SPEC (\<lambda>r. r=x*5)"
    unfolding test2_def i_test2_def
    apply (refine_vcg WHILEIT_rule[where R="measure (nat o fst)"])  
    apply auto  
    done
    