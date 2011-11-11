Require Import Program Omega Arith List Classical.

Program Fixpoint list_at idx (vec : list bool) (wit : 0 <= idx < length vec) : bool :=
match idx with
| 0 =>
  match vec with
  | cons x xs => x
  | nil => _
  end
| S idx_ =>
  match vec with
  | cons x xs => list_at idx_ xs _
  | nil => _
  end
end.
Next Obligation.
simpl in *.
contradict H0.
omega.
Defined.
Next Obligation.
simpl in *.
omega.
Defined.
Next Obligation.
simpl in *.
contradict H0.
omega.
Defined.

Program Fixpoint update idx (val : bool) (vec : list bool) (wit : 0 <= idx < length vec) :
{ l : list bool | length l = length vec /\
(forall i , 0 <= i < length vec /\ idx <> i -> exists pr pr' , list_at i l pr = list_at i vec pr') /\
exists pr , list_at idx l pr = val } :=
match idx with
| 0 =>
  match vec with
  | cons x xs => cons val xs
  | nil => _
  end
| S idx_ =>
  match vec with
  | cons x xs => cons x (update idx_ val xs _)
  | nil => _
  end
end.
Next Obligation.
split.
 trivial.
 
 split.
  intros.
  assert (0 <= i < length (val :: xs)) as pr.
   simpl.
   omega.
   
   assert (0 <= i < length (x :: xs)) as pr'.
    simpl.
    omega.
    
    exists pr pr'.
    destruct H1.
    destruct i.
     contradict H2.
     trivial.
     
     simpl.
     apply f_equal.
     apply proof_irrelevance.
     
  constructor.
   omega.
   
   trivial.
Defined.
Next Obligation.
simpl in H0.
contradict H0.
omega.
Defined.
Next Obligation.
simpl in H0.
omega.
Defined.
Next Obligation.
split.
 simpl in *.
 omega.
 
 split.
  intros.
  destruct H1.
  assert (0 <= i < length (x :: x0)) as pr.
   simpl.
   omega.
   
   assert (0 <= i < length (x :: xs)) as pr'.
    simpl in *.
    omega.
    
    exists pr pr'.
    destruct i.
     simpl.
     trivial.
     
     simpl in *.
     assert (0 <= i < length xs /\ idx_ <> i).
      omega.
      
      destruct (e0 i H3).
      destruct H4.
      cut
       (list_at_obligation_2 (S i) (x :: x0) pr i eq_refl x x0 eq_refl = x1).
       intros.
       rewrite H5.
       rewrite H4.
       cut
        (x2 = list_at_obligation_2 (S i) (x :: xs) pr' i eq_refl x xs eq_refl).
        intros.
        rewrite H6.
        trivial.
        
        apply proof_irrelevance.
        
       apply proof_irrelevance.
       
  simpl in H0.
  assert (0 <= S idx_ < S (length x0)).
   omega.
   
   exists H1.
   apply f_equal.
   apply proof_irrelevance.
Defined.
Next Obligation.
simpl in H0.
contradict H0.
omega.
Defined.

Definition Inv1 (vec : list bool) i : Prop :=
forall idx , (0 <= idx < length vec /\ idx < i) -> exists wit , list_at idx vec wit = false.

Lemma Inv1_lem (vec : list bool) i (i_wit : 0 <= i < length vec) :
Inv1 vec i -> list_at i vec i_wit = false -> Inv1 vec (i + 1).
intros.
unfold Inv1.
intros.
destruct H1.
exists H1.
assert (idx < i \/ idx = i).
 omega.
 
 destruct H3.
  unfold Inv1 in H.
  assert (0 <= idx < length vec /\ idx < i).
   omega.
   
   destruct (H idx H4).
   cut (x = H1).
    intros.
    rewrite <- H6.
    trivial.
    
    apply proof_irrelevance.
    
  destruct H3.
  cut (H1 = i_wit).
   intros.
   rewrite H3.
   trivial.
   
   apply proof_irrelevance.
Qed.

Definition Inv2 (vec : list bool) j : Prop :=
forall idx , (j < idx < length vec) -> exists wit , list_at idx vec wit = true.

Lemma Inv2_lem (vec: list bool) j (j_wit : 0 <= j < length vec) :
Inv2 vec j -> list_at j vec j_wit = true -> Inv2 vec (j - 1).
Proof.
intros.
unfold Inv2.
intros.
assert (0 <= idx < length vec).
 omega.
 
 exists H2.
 unfold Inv2 in H.
 assert (j = idx \/ j < idx < length vec).
  omega.
  
  destruct H3.
   destruct H3.
   rewrite <- H0.
   apply f_equal.
   apply proof_irrelevance.
   
   destruct (H idx H3).
   rewrite <- H4.
   apply f_equal.
   apply proof_irrelevance.
Qed.

Program Definition swap (vec : list bool) i j (wit : 0 <= i < length vec /\ 0 <= j < length vec /\ i <= j)
(inv1 : Inv1 vec i) (inv2 : Inv2 vec j)
:
{ l : list bool | length l = length vec /\ Inv1 l i /\ Inv2 vec j }
:=
  let t := list_at i vec _ in
  let aj := list_at j vec _ in
  update j t (update i aj vec _) _.
Next Obligation.
destruct update ; simpl in *.
omega.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
simpl in *.
split.
 omega.
 
 split.
  destruct a.
  destruct H0.
  destruct H1.
  destruct a0.
  destruct H3.
  destruct H4.
  unfold Inv1.
  intros.
  destruct H5.
  exists H5.
  unfold Inv1 in inv1.
  assert (0 <= idx < length x /\ j <> idx).
   omega.
   
   destruct (H3 idx H7).
   destruct H8.
   assert (H5 = x3) as H9.
    apply proof_irrelevance.
    
    rewrite H9.
    rewrite H8.
    assert (0 <= idx < length vec /\ i <> idx).
     omega.
     
     destruct (H0 idx H10).
     destruct H11.
     assert (x4 = x5).
      apply proof_irrelevance.
      
      rewrite H12.
      rewrite H11.
      assert (0 <= idx < length vec /\ idx < i).
       omega.
       
       destruct (inv1 idx H13).
       rewrite <- H14.
       apply f_equal.
       apply proof_irrelevance.
       
  unfold Inv2.
  intros.
  assert (0 <= idx < length vec).
   omega.
   
   exists H0.
   unfold Inv2 in inv2.
   destruct (inv2 idx H).
   rewrite <- H1.
   apply f_equal.
   apply proof_irrelevance.
Defined.

Definition bool_lt (b1 b2 : bool) : Prop :=
match b1 , b2 with
| true , false => False
| _ , _ => True
end.

Definition is_sorted (vec : list bool) :=
forall i j (i_wit : 0 <= i < length vec) (j_wit : 0 <= j < length vec) (wit : i < j) ,
bool_lt (list_at i vec i_wit) (list_at j vec j_wit).

Program Fixpoint sort_impl (vec : list bool)
i (i_wit : 0 <= i < length vec) (inv1 : Inv1 vec i)
j (j_wit : 0 <= j < length vec) (inv2 : Inv2 vec j)
(wit : i <= j)
{measure (j - i)} : { l : list bool | is_sorted l } :=
  match eq_nat_dec i j with
    | left _ => vec (* i = j *)
    | right _ => (* i < j *)
    match list_at i vec _ with
      | false =>
        match le_lt_dec (i + 1) j with
        | left _ => sort_impl vec (i + 1) _ _ j j_wit _ _ (* i + 1 < j *)
        | right _ => vec (* そもそもここには到達しないのでは *) (* i + 1 >= j *)
        end
      | true =>
        match list_at j vec _ with
          | true =>
      	    match le_lt_dec i (j - 1) with
      	    | left _ => sort_impl vec i i_wit _ (j - 1) _ _ _
      	    | right _ => vec
	    end
          | false =>
          let swapped := swap vec i j _ inv1 inv2 in
	  match le_lt_dec (i + 1) (j - 1) with
	  | left _ => sort_impl swapped (i+1) _ _ (j-1) _ _ _
	  | right _ => swapped
	  end
        end
    end
  end.
Next Obligation.
unfold is_sorted.
intros.
assert (j0 < j \/ j0 = j \/ j < j0).
 omega.
 
 destruct H3.
  assert (i < j).
   omega.
   
   cut (list_at i vec i_wit = false).
    cut (list_at j0 vec j_wit = false).
     intros.
     rewrite H6.
     rewrite H5.
     simpl.
     trivial.
     
     unfold Inv1 in inv1.
     assert (0 <= j0 < length vec /\ j0 < j).
      omega.
      
      destruct (inv1 j0 H5).
      rewrite <- H6.
      apply f_equal; apply proof_irrelevance.
      
    unfold Inv1 in inv1.
    assert (0 <= i < length vec /\ i < j).
     omega.
     
     destruct (inv1 i H5).
     rewrite <- H6.
     apply f_equal; apply proof_irrelevance.
     
  destruct H3.
   destruct H3.
   assert (list_at i vec i_wit = false).
    unfold Inv1 in inv1.
    assert (0 <= i < length vec /\ i < j0).
     omega.
     
     destruct (inv1 i H3).
     rewrite <- H4.
     apply f_equal; apply proof_irrelevance.
     
    rewrite H3.
    simpl.
    trivial.
    
   assert (list_at j0 vec j_wit = true).
    unfold Inv2 in inv2.
    assert (j < j0 < length vec).
     omega.
     
     destruct (inv2 j0 H4).
     rewrite <- H5.
     apply f_equal; apply proof_irrelevance.
     
    rewrite H4.
    destruct (list_at i vec i_wit); simpl; trivial.
Defined.
Next Obligation.
omega.
Defined.
Next Obligation.
assert (0 <= i < length vec).
 omega.
 
 apply (Inv1_lem vec i H).
  trivial.
  
  rewrite Heq_anonymous0.
  apply f_equal; apply proof_irrelevance.
Defined.
Next Obligation.
omega.
Defined.
Next Obligation.
unfold is_sorted.
intros.
assert (i < j).
 omega.
 
 contradict H.
 omega.
Defined.
Next Obligation.
omega.
Defined.
Next Obligation.
assert (0 <= j < length vec).
 omega.
 
 apply (Inv2_lem vec j H).
  trivial.
  
  rewrite Heq_anonymous1.
  apply f_equal; apply proof_irrelevance.
Defined.
Next Obligation.
omega.
Defined.
Next Obligation.
assert (i < j).
 omega.
 
 contradict H.
 omega.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
omega.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
unfold Inv1.
intros.
assert (0 <= idx < length x0).
 omega.
 
 exists H0.
 destruct a.
 destruct H2.
 destruct a0.
 destruct H5.
 destruct H3.
 destruct H6.
 assert (0 <= idx < length x /\ j <> idx).
  omega.
  
  destruct (H5 idx H7).
  destruct H8.
  assert (H0 = x3).
   apply proof_irrelevance.
   
   rewrite H9.
   rewrite H8.
   assert (idx < i \/ idx = i).
    omega.
    
    destruct H10.
     assert (0 <= idx < length vec /\ i <> idx).
      omega.
      
      destruct (H2 idx H11).
      destruct H12.
      assert (x4 = x5).
       apply proof_irrelevance.
       
       rewrite H13.
       rewrite H12.
       unfold Inv1 in inv1.
       assert (0 <= idx < length vec /\ idx < i).
        omega.
        
        destruct (inv1 idx H14).
        rewrite <- H15.
        apply f_equal; apply proof_irrelevance.
        
     destruct H10.
     assert (x4 = x1).
      apply proof_irrelevance.
      
      rewrite H10.
      rewrite H3.
      auto.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
omega.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
destruct a.
destruct H0.
destruct H1.
destruct a0.
destruct H3.
destruct H4.
unfold Inv2.
intros.
assert (0 <= idx < length x0).
 omega.
 
 exists H6.
 assert (j = idx \/ j < idx).
  omega.
  
  destruct H7.
   destruct H7.
   assert (H6 = x2).
    apply proof_irrelevance.
    
    rewrite H7.
    rewrite H4.
    auto.
    
   assert (0 <= idx < length x /\ j <> idx).
    omega.
    
    destruct (H3 idx H8).
    destruct H9.
    assert (x3 = H6).
     apply proof_irrelevance.
     
     destruct H10.
     rewrite H9.
     assert (0 <= idx < length vec /\ i <> idx).
      omega.
      
      destruct (H0 idx H6).
      destruct H10.
      assert (x5 = x4).
       apply proof_irrelevance.
       
       destruct H11.
       rewrite H10.
       unfold Inv2 in inv2.
       assert (j < idx < length vec).
        omega.
        
        destruct (inv2 idx H11).
        rewrite <- H12.
        apply f_equal; apply proof_irrelevance.
Defined.
Next Obligation.
omega.
Defined.
Next Obligation.
destruct update; simpl in *.
destruct update; simpl in *.
unfold is_sorted.
intros.
assert (i < j).
 omega.
 
 assert (j = i + 1).
  omega.
  
  dependent destruction H0.
  simpl in *.
  destruct a.
  destruct H1.
  destruct a0.
  destruct H4.
  assert (Inv1 x0 i).
   unfold Inv1.
   intros.
   assert (0 <= idx < length x /\ i + 1 <> idx).
    omega.
    
    destruct (H4 idx H7).
    destruct H8.
    assert (0 <= idx < length x0).
     omega.
     
     exists H9.
     assert (H9 = x1).
      apply proof_irrelevance.
      
      rewrite H10.
      rewrite H8.
      assert (0 <= idx < length vec /\ i <> idx).
       omega.
       
       destruct (H1 idx H11).
       destruct H12.
       assert (x3 = x2).
        apply proof_irrelevance.
        
        destruct H13.
        rewrite H12.
        unfold Inv1 in inv1.
        assert (0 <= idx < length vec /\ idx < i).
         omega.
         
         destruct (inv1 idx H13).
         rewrite <- H14.
         apply f_equal; apply proof_irrelevance.
         
   assert (Inv2 x0 (i + 1)).
    unfold Inv2.
    intros.
    assert (0 <= idx < length x0).
     omega.
     
     exists H8.
     assert (0 <= idx < length x /\ i + 1 <> idx).
      omega.
      
      destruct (H4 idx H9).
      destruct H10.
      assert (H8 = x1).
       apply proof_irrelevance.
       
       rewrite H11.
       rewrite H10.
       assert (0 <= idx < length vec /\ i <> idx).
        omega.
        
        destruct (H1 idx H12).
        destruct H13.
        assert (x2 = x3).
         apply proof_irrelevance.
         
         rewrite H14.
         rewrite H13.
         unfold Inv2 in inv2.
         assert (i + 1 < idx < length vec).
          omega.
          
          destruct (inv2 idx H15).
          rewrite <- H16.
          apply f_equal; apply proof_irrelevance.
          
    destruct H2.
    destruct H5.
    rewrite <- Heq_anonymous1 in H2.
    rewrite <- Heq_anonymous0 in H5.
    assert (exists pr : _, list_at i x0 pr = false).
     assert (0 <= i < length x0).
      omega.
      
      exists H8.
      assert (0 <= i < length x /\ i + 1 <> i).
       omega.
       
       destruct (H4 i H9).
       destruct H10.
       assert (H8 = x3).
        apply proof_irrelevance.
        
        rewrite H11.
        rewrite H10.
        rewrite <- H2.
        apply f_equal; apply proof_irrelevance.
        
     destruct H8.
     clear H.
     assert (j0 <= i \/ i < j0).
      omega.
      
      destruct H.
       destruct H.
        assert (j_wit = x3).
         apply proof_irrelevance.
         
         rewrite H.
         rewrite H8.
         unfold Inv1 in H6.
         assert (0 <= i0 < length x0 /\ i0 < j0).
          omega.
          
          destruct (H6 i0 H9).
          assert (i_wit = x4).
           apply proof_irrelevance.
           
           rewrite H11.
           rewrite H10.
           simpl; auto.
           
        assert (j0 < S m).
         omega.
         
         cut (list_at i0 x0 i_wit = false).
          cut (list_at j0 x0 j_wit = false).
           intros.
           rewrite H10; rewrite H11.
           simpl; trivial.
           
           unfold Inv1 in H6.
           assert (0 <= j0 < length x0 /\ j0 < S m).
            omega.
            
            destruct (H6 j0 H10).
            assert (j_wit = x4).
             apply proof_irrelevance.
             
             rewrite H12.
             trivial.
             
          unfold Inv1 in H6.
          assert (0 <= i0 < length x0 /\ i0 < S m).
           omega.
           
           destruct (H6 i0 H10).
           assert (i_wit = x4).
            apply proof_irrelevance.
            
            rewrite H12.
            trivial.
            
       assert (i + 1 = j0 \/ i + 1 < j0).
        omega.
        
        destruct H9.
         destruct H9.
         assert (j_wit = x2).
          apply proof_irrelevance.
          
          rewrite H9.
          rewrite H5.
          destruct (list_at i0 x0 i_wit); (simpl; trivial).
          
         assert (list_at j0 x0 j_wit = true).
          unfold Inv2 in H7.
          assert (i + 1 < j0 < length x0).
           omega.
           
           destruct (H7 j0 H10).
           assert (j_wit = x4).
            apply proof_irrelevance.
            
            rewrite H12; trivial.
            
          rewrite H10.
          destruct (list_at i0 x0 i_wit); (simpl; trivial).
Defined.

Program Definition sort (vec : list bool) : { l : list bool | is_sorted l} :=
match vec with
| nil => nil
| cons _ _ => sort_impl vec 0 _ _ (length vec - 1) _ _ _
end.
Next Obligation.
unfold is_sorted.
intros.
simpl in *.
contradict i_wit.
omega.
Defined.
Next Obligation.
simpl ; omega.
Defined.
Next Obligation.
unfold Inv1.
intros.
simpl in *.
destruct H.
contradict H0.
omega.
Defined.
Next Obligation.
simpl in *.
omega.
Defined.
Next Obligation.
simpl in *.
unfold Inv2.
intros.
simpl in *.
contradict H.
omega.
Defined.
Next Obligation.
simpl in *.
omega.
Defined.

