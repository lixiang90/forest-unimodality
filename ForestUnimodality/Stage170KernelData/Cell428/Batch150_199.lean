import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell428.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch150_199
import ForestUnimodality.BinomialMassData.Q9_35.Batch150_199

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167680137347119117797/50000000000000000000)
  centralHi := (67072054938847647119/20000000000000000000)
  directionLo := (336491341226356758667/100000000000000000000)
  directionHi := (84122835306589189667/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree150.table
  base := (-760442803891398187832761925724950418153/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11042452840665044795642746170000000000000)
      constant := (197371355500428294662818859406700396654776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree150.table
  base := (-6083542478618530176100359461293955191489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-556807758100892879228605006980000000000000)
      constant := (10259350674672756589237738227196596195617039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336491341226356758667/100000000000000000000)
  centralHi := (84122835306589189667/25000000000000000000)
  directionLo := (168809309279457388041/50000000000000000000)
  directionHi := (337618618558914776083/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree151.table
  base := (-1201213635372047592898041407611962535473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2223469205188538182216273467000000000000)
      constant := (40043760922605041832866252392513037464527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree151.table
  base := (-6006068218611877148887138713639716158917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-560582374638886243446711513696000000000000)
      constant := (10406811359051054189058012453632853908213067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168809309279457388041/50000000000000000000)
  centralHi := (337618618558914776083/100000000000000000000)
  directionLo := (338742144521385951149/100000000000000000000)
  directionHi := (6774842890427719023/2000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree152.table
  base := (-5927172214195474821491112509100959404647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11192239211220337026519988500000000000000)
      constant := (203086398730335350799530525970899040595353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree152.table
  base := (-5927172250902631372396077462436715815139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-564356991176879607664818020412000000000000)
      constant := (10555312322787977127248985395041400925058189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338742144521385951149/100000000000000000000)
  centralHi := (6774842890427719023/2000000000000000000)
  directionLo := (339861956317951332193/100000000000000000000)
  directionHi := (169930978158975666097/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree153.table
  base := (-5846854572825361848502678681406484857001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11267132396497983141958609665000000000000)
      constant := (205974137822670253793578784569218515142999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree153.table
  base := (-182714206409255157300876595521367098539/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-142032901928718242970731131782000000000000)
      constant := (2676213391108215541661903539830324097372712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339861956317951332193/100000000000000000000)
  centralHi := (169930978158975666097/50000000000000000000)
  directionLo := (340978090541874248339/100000000000000000000)
  directionHi := (17048904527093712417/5000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree154.table
  base := (-5765115281952137081188343742465379968067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11342025581775629257397230830000000000000)
      constant := (208882021860827680110812599570034620031933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree154.table
  base := (-5765115310321583833005294576961792725661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-81700889178980905157290147692000000000000)
      constant := (1550776440365483303990458461074867450920373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340978090541874248339/100000000000000000000)
  centralHi := (17048904527093712417/5000000000000000000)
  directionLo := (342090583189453091407/100000000000000000000)
  directionHi := (21380661449340818213/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree155.table
  base := (-22195134259003558757287166722633822473/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11416918767053275372835851995000000000000)
      constant := (211810050816078519228914563984630741446912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree155.table
  base := (-5681954395243636748888258942479878824053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-575680840790859700319137540560000000000000)
      constant := (11007056875759967311166108504608485937621403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342090583189453091407/100000000000000000000)
  centralHi := (21380661449340818213/6250000000000000000)
  directionLo := (171599734836783517757/50000000000000000000)
  directionHi := (68639893934713407103/20000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree156.table
  base := (-699671483269013001172380276330295528021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11491811952330921488274473160000000000000)
      constant := (214758224660154350869039827099357635775832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree156.table
  base := (-1119474377614820924463680707370042338009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-579455457328853064537244047276000000000000)
      constant := (11159718942655237455135280480777539627187795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171599734836783517757/50000000000000000000)
  centralHi := (68639893934713407103/20000000000000000000)
  directionLo := (344304784836829115753/100000000000000000000)
  directionHi := (172152392418414557877/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree157.table
  base := (-1377841949328319497556806451844351639041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11566705137608567603713094325000000000000)
      constant := (217726543365235613024690089438247593443836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree157.table
  base := (-5511367816582708401101104983024750184089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-583230073866846428755350553992000000000000)
      constant := (11313421281883477233398261701506587240979639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344304784836829115753/100000000000000000000)
  centralHi := (172152392418414557877/50000000000000000000)
  directionLo := (345406562964360487373/100000000000000000000)
  directionHi := (172703281482180243687/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree158.table
  base := (-5423942191170414618589360240951283606509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11641598322886213719151715490000000000000)
      constant := (220715006903940324061686056231548716393491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree158.table
  base := (-1355985552026893359711218787504746549129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-146751172601209948243364265177000000000000)
      constant := (2867040973026279625907058771303467419092679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345406562964360487373/100000000000000000000)
  centralHi := (172703281482180243687/50000000000000000000)
  directionLo := (346504837796199115579/100000000000000000000)
  directionHi := (17325241889809955779/5000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree159.table
  base := (-666886884334835570004492320956954503417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11716491508163859834590336655000000000000)
      constant := (223723615249313313314457234422969363972664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree159.table
  base := (-2667547544782641172222714874057341688671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-295389653471416578595781783712000000000000)
      constant := (5811973386000624358994655281047790257255121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346504837796199115579/100000000000000000000)
  centralHi := (17325241889809955779/5000000000000000000)
  directionLo := (173799821269677800873/50000000000000000000)
  directionHi := (347599642539355601747/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree160.table
  base := (-5244826474376749021510301465018560858053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11791384693441505950028957820000000000000)
      constant := (226752368374815919576060283334981439141947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree160.table
  base := (-5244826487460545451975797778686619742711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-594553923480826521409670074140000000000000)
      constant := (11780769920273137070111909711084355632607161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173799821269677800873/50000000000000000000)
  centralHi := (347599642539355601747/100000000000000000000)
  directionLo := (34869100987952833329/10000000000000000000)
  directionHi := (348691009879528333291/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree161.table
  base := (-2576568208198314797150065737195863036489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11866277878719152065467578985000000000000)
      constant := (229801266254316121255207520426233273927022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree161.table
  base := (-5153136427895514969749099162534502806063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-85475505716974269375396654408000000000000)
      constant := (1705519047948825443112669950865858480357559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/10000000000000000000)
  centralHi := (348691009879528333291/100000000000000000000)
  directionLo := (21861185749530603127/6250000000000000000)
  directionHi := (349778971992489650033/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree162.table
  base := (-2530012463236589401881794632923888332887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-11941171063996798180906200150000000000000)
      constant := (232870308862079065826540785026652223334226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree162.table
  base := (-253001246828938310917206986640587491881/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-150525789139203312461470771893000000000000)
      constant := (3024384254211862905577822227800256064489155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21861185749530603127/6250000000000000000)
  centralHi := (349778971992489650033/100000000000000000000)
  directionLo := (87715890138788562139/25000000000000000000)
  directionHi := (350863560555154248557/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree163.table
  base := (-993098405990636068976111813350585468207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2403212849854888859268964263000000000000)
      constant := (47191899234551593919016038581774414531793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree163.table
  base := (-4965492038833967034784632759691862305123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-605877773094806614063989594288000000000000)
      constant := (12257480962649297907665545526265898747048973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87715890138788562139/25000000000000000000)
  centralHi := (350863560555154248557/100000000000000000000)
  directionLo := (35194480675634059651/10000000000000000000)
  directionHi := (351944806756340596511/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree164.table
  base := (-2434768875902052494950265341755067272131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12090957434552090411783442480000000000000)
      constant := (239068828161385361788576254266489865455738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree164.table
  base := (-2434768879804127182052308833295199947657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-304826194816399989141048050502000000000000)
      constant := (6209232585912453623772395784754135202564807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35194480675634059651/10000000000000000000)
  centralHi := (351944806756340596511/100000000000000000000)
  directionLo := (353022741307235699839/100000000000000000000)
  directionHi := (551598033292555781/156250000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree165.table
  base := (-149130066144454547315405826747376351437/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12165850619829736527222063645000000000000)
      constant := (242198304803364649631759486759708956754016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree165.table
  base := (-238608106174016762277255649625888409223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-153356751542698335625050651930000000000000)
      constant := (3145122410792480749256554283129157339740365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353022741307235699839/100000000000000000000)
  centralHi := (551598033292555781/156250000000000000)
  directionLo := (177048697225786578337/50000000000000000000)
  directionHi := (14163895778062926267/4000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree166.table
  base := (-4673365148642351654454985584670140834137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12240743805107382642660684810000000000000)
      constant := (245347926074461983387632831187829859165863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree166.table
  base := (-4673365154668327798170715538183355109983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-617201622708786706718309114436000000000000)
      constant := (12743554375497657368275656972056215599610833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177048697225786578337/50000000000000000000)
  centralHi := (14163895778062926267/4000000000000000000)
  directionLo := (177584397987767020393/50000000000000000000)
  directionHi := (355168795975534040787/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree167.table
  base := (-2286573435871242028262122210234270898347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12315636990385028758099305975000000000000)
      constant := (248517691950798402410658571200156458203306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree167.table
  base := (-457314687703735639356503516870826028009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-310488119623390035468207810576000000000000)
      constant := (6453829683819359633542757102368047623137795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177584397987767020393/50000000000000000000)
  centralHi := (355168795975534040787/100000000000000000000)
  directionLo := (356236975217379784461/100000000000000000000)
  directionHi := (178118487608689892231/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree168.table
  base := (-4471507309454604342773671244072770017337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12390530175662674873537927140000000000000)
      constant := (251707602408842245078363798515927229982663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree168.table
  base := (-4471507314106913948175888734501552000171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-89250122254967633593503161124000000000000)
      constant := (1867543516920093362935692257840889135998803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356236975217379784461/100000000000000000000)
  centralHi := (178118487608689892231/50000000000000000000)
  directionLo := (357301961076825874197/100000000000000000000)
  directionHi := (178650980538412937099/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree169.table
  base := (-4368446484970416823611621059794059012539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12465423360940320988976548305000000000000)
      constant := (254917657425401807080340158130830940987461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree169.table
  base := (-2184223244529001577482041755707705938763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-314262736161383399686314317292000000000000)
      constant := (6619495063383795528356786107994922409000613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357301961076825874197/100000000000000000000)
  centralHi := (178650980538412937099/50000000000000000000)
  directionLo := (358363782024164832181/100000000000000000000)
  directionHi := (179181891012082416091/50000000000000000000)

def endpointA : IntegerEndpointWitness 170 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree170.table
  base := (-4263964421148775943099049099343469980873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12540316546217967104415169470000000000000)
      constant := (258147856977618233972526694813156530019127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 170 interval.damping) (curvature.centralUpper 170 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree170.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 170 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree170.table
  base := (-532995553092508435684691015419659390223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-158075022215190040897683785325000000000000)
      constant := (3351553972874977271367711478868873379758146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 170 interval.damping) (curvature.centralUpper 170 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree170.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 170 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel171
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358363782024164832181/100000000000000000000)
  centralHi := (179181891012082416091/50000000000000000000)
  directionLo := (179711233054573315527/50000000000000000000)
  directionHi := (71884493221829326211/20000000000000000000)

def endpointA : IntegerEndpointWitness 171 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree171.table
  base := (-415806114052257228402632917525589647103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2523041946299122643970758127000000000000)
      constant := (52279640208591727034426606950073820705794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 171 interval.damping) (curvature.centralUpper 171 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree171.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 171 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree171.table
  base := (-2079030571838860957101442036469244600379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-318037352699376763904420824008000000000000)
      constant := (6787240955766950746535910244857607014581429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 171 interval.damping) (curvature.centralUpper 171 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree171.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 171 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel172
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179711233054573315527/50000000000000000000)
  centralHi := (71884493221829326211/20000000000000000000)
  directionLo := (360478040969624378417/100000000000000000000)
  directionHi := (180239020484812189209/50000000000000000000)

def endpointA : IntegerEndpointWitness 172 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree172.table
  base := (-4050736665305408831298122747389470224163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12690102916773259335292411800000000000000)
      constant := (264668689599209407694254516482610529775837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 172 interval.damping) (curvature.centralUpper 172 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree172.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 172 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree172.table
  base := (-4050736668077292533523770039552171564903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-639849321936746892026948154732000000000000)
      constant := (13743788185781458300989698623418743593319753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 172 interval.damping) (curvature.centralUpper 172 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree172.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 172 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360478040969624378417/100000000000000000000)
  centralHi := (180239020484812189209/50000000000000000000)
  directionLo := (22595658364998300629/6250000000000000000)
  directionHi := (72306106767994562013/20000000000000000000)

def endpointA : IntegerEndpointWitness 173 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree173.table
  base := (-3941991017398078191626764124312836953863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12764996102050905450731032965000000000000)
      constant := (267959322624469758932178805701312163046137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 173 interval.damping) (curvature.centralUpper 173 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree173.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 173 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree173.table
  base := (-985497754958293382060633060246541058967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-160905984618685064061263665362000000000000)
      constant := (3478533678292438548542291337978619488110617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 173 interval.damping) (curvature.centralUpper 173 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree173.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 173 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel174
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22595658364998300629/6250000000000000000)
  centralHi := (72306106767994562013/20000000000000000000)
  directionLo := (90644992889821711613/25000000000000000000)
  directionHi := (362579971559286846453/100000000000000000000)

def endpointA : IntegerEndpointWitness 174 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree174.table
  base := (-3831824218394850576267975616311945441511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12839889287328551566169654130000000000000)
      constant := (271270100097145418674650180096188054558489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 174 interval.damping) (curvature.centralUpper 174 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree174.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 174 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree174.table
  base := (-3831824220534009353131266186675411702443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-647398555012733620463161168164000000000000)
      constant := (14085521492640945594326387995240104826580293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 174 interval.damping) (curvature.centralUpper 174 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree174.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 174 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel175
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90644992889821711613/25000000000000000000)
  centralHi := (362579971559286846453/100000000000000000000)
  directionLo := (181813190289683597349/50000000000000000000)
  directionHi := (363626380579367194699/100000000000000000000)

def endpointA : IntegerEndpointWitness 175 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree175.table
  base := (-744047257917916311778319325781376321547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2582956494521239536321655059000000000000)
      constant := (54920204399188506269599760052343623678453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 175 interval.damping) (curvature.centralUpper 175 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree175.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 175 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree175.table
  base := (-3720236291468709396542659393418487084101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-93024738792960997811609667840000000000000)
      constant := (2036849789021696563061726409296070590411293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 175 interval.damping) (curvature.centralUpper 175 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree175.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 175 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel176
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181813190289683597349/50000000000000000000)
  centralHi := (363626380579367194699/100000000000000000000)
  directionLo := (364669786972499717969/100000000000000000000)
  directionHi := (36466978697249971797/10000000000000000000)

def endpointA : IntegerEndpointWitness 176 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree176.table
  base := (-3607227251981647911013936847596386677193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-12989675657883843797046896460000000000000)
      constant := (277952088299861720180708356512403613322807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 176 interval.damping) (curvature.centralUpper 176 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree176.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 176 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree176.table
  base := (-90180681340807547745389277863318067519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-163736947022180087224843545399000000000000)
      constant := (3607853950918447212792662964499774146915690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 176 interval.damping) (curvature.centralUpper 176 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree176.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 176 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel177
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364669786972499717969/100000000000000000000)
  centralHi := (36466978697249971797/10000000000000000000)
  directionLo := (14628408657561401791/4000000000000000000)
  directionHi := (45713777054879380597/12500000000000000000)

def endpointA : IntegerEndpointWitness 177 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree177.table
  base := (-873199281570429795691642064123394308311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13064568843161489912485517625000000000000)
      constant := (281323298988192315622647276864131422766756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 177 interval.damping) (curvature.centralUpper 177 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree177.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 177 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree177.table
  base := (-3492797127731633529387607722161760805639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-658722404626713713117480688312000000000000)
      constant := (14605923333192048838356646261784873720523689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 177 interval.damping) (curvature.centralUpper 177 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree177.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 177 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14628408657561401791/4000000000000000000)
  centralHi := (45713777054879380597/12500000000000000000)
  directionLo := (366747694314774651987/100000000000000000000)
  directionHi := (91686923578693662997/25000000000000000000)

def endpointA : IntegerEndpointWitness 178 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree178.table
  base := (-422118241614671516019181352324734920911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13139462028439136027924138790000000000000)
      constant := (284714654040506740919811601353902120632712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 178 interval.damping) (curvature.centralUpper 178 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree178.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 178 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree178.table
  base := (-3376945934190920310098210152562793310249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-662497021164707077335587195028000000000000)
      constant := (14781471110705869316302935470553223127797799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 178 interval.damping) (curvature.centralUpper 178 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree178.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 178 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366747694314774651987/100000000000000000000)
  centralHi := (91686923578693662997/25000000000000000000)
  directionLo := (367782245578169426779/100000000000000000000)
  directionHi := (18389112278908471339/5000000000000000000)

def endpointA : IntegerEndpointWitness 179 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree179.table
  base := (-407459211504819320458169943593082599931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13214355213716782143362759955000000000000)
      constant := (288126153436655048255710554966880339200552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 179 interval.damping) (curvature.centralUpper 179 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree179.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 179 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree179.table
  base := (-3259673693157155819005832033904295435887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-666271637702700441553693701744000000000000)
      constant := (14958059135228047600223655256523889523641537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 179 interval.damping) (curvature.centralUpper 179 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree179.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 179 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367782245578169426779/100000000000000000000)
  centralHi := (18389112278908471339/5000000000000000000)
  directionLo := (368813894857336493711/100000000000000000000)
  directionHi := (23050868428583530857/6250000000000000000)

def endpointA : IntegerEndpointWitness 180 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree180.table
  base := (-3140980423522904790305021995012931971309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13289248398994428258801381120000000000000)
      constant := (291557797156759599329341410154987068028691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 180 interval.damping) (curvature.centralUpper 180 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree180.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 180 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree180.table
  base := (-196311276531586344033775241366799162649/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-167511563560173451442950052115000000000000)
      constant := (3783921851446176664786434756352107364120796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 180 interval.damping) (curvature.centralUpper 180 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree180.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 180 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel181
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368813894857336493711/100000000000000000000)
  centralHi := (23050868428583530857/6250000000000000000)
  directionLo := (184921333218449941669/50000000000000000000)
  directionHi := (369842666436899883339/100000000000000000000)

def endpointA : IntegerEndpointWitness 181 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree181.table
  base := (-3020866146980932295773124873215618957461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13364141584272074374240002285000000000000)
      constant := (295009585181209884653003480202409381042539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 181 interval.damping) (curvature.centralUpper 181 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree181.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 181 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree181.table
  base := (-755216536960956063001710840523055152111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-168455217694671792497476678794000000000000)
      constant := (3828588980353760843922311452162670297546561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 181 interval.damping) (curvature.centralUpper 181 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree181.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 181 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184921333218449941669/50000000000000000000)
  centralHi := (369842666436899883339/100000000000000000000)
  directionLo := (370868584264660417643/100000000000000000000)
  directionHi := (92717146066165104411/25000000000000000000)

def endpointA : IntegerEndpointWitness 182 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree182.table
  base := (-1449665440880532540247215503800918919159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13439034769549720489678623450000000000000)
      constant := (298481517490657476226272002284898162161682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 182 interval.damping) (curvature.centralUpper 182 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree182.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 182 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree182.table
  base := (-2899330882518905759825781953693117997391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (104)
      previous := (36)
      next := (0)
      square := (1048504593887045616140696310000000000000)
      linear := (-96799355330954362029716174556000000000000)
      constant := (2213437811595869012375937809530548174018263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 182 interval.damping) (curvature.centralUpper 182 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree182.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 182 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370868584264660417643/100000000000000000000)
  centralHi := (92717146066165104411/25000000000000000000)
  directionLo := (371891671958099994799/100000000000000000000)
  directionHi := (929729179895249987/250000000000000000)

def endpointA : IntegerEndpointWitness 183 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree183.table
  base := (-2776374646954568613746453796626137958887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13513927954827366605117244615000000000000)
      constant := (301973594066011108579869463003998862041113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 183 interval.damping) (curvature.centralUpper 183 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree183.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 183 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree183.table
  base := (-1388187323810064059208349077875981546513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-340685051927336949213059864304000000000000)
      constant := (7837406842058720094771070576081476904220863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 183 interval.damping) (curvature.centralUpper 183 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree183.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 183 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel184
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371891671958099994799/100000000000000000000)
  centralHi := (929729179895249987/250000000000000000)
  directionLo := (186455976405362635473/50000000000000000000)
  directionHi := (372911952810725270947/100000000000000000000)

def endpointA : IntegerEndpointWitness 184 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree184.table
  base := (-1325998730700170560137230516543864882861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13588821140105012720555865780000000000000)
      constant := (305485814888431883489050594566912270234278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 184 interval.damping) (curvature.centralUpper 184 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree184.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 184 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree184.table
  base := (-530399492396967948509560580423675779969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-685144720392667262644226235324000000000000)
      constant := (15856602929331084612097332929239399433907595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 184 interval.damping) (curvature.centralUpper 184 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree184.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 184 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel185
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186455976405362635473/50000000000000000000)
  centralHi := (372911952810725270947/100000000000000000000)
  directionLo := (93482362449563889843/25000000000000000000)
  directionHi := (373929449798255559373/100000000000000000000)

def endpointA : IntegerEndpointWitness 185 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree185.table
  base := (-2526199343689589619947938235611964425511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13663714325382658835994486945000000000000)
      constant := (309018179939328593933945911455013035574489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 185 interval.damping) (curvature.centralUpper 185 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree185.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 185 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree185.table
  base := (-2526199344202885596013894371698431462977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-688919336930660626862332742040000000000000)
      constant := (16039432415901113951071194887176776858314127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 185 interval.damping) (curvature.centralUpper 185 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree185.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 185 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93482362449563889843/25000000000000000000)
  centralHi := (373929449798255559373/100000000000000000000)
  directionLo := (374944185584659597449/100000000000000000000)
  directionHi := (7498883711693191949/2000000000000000000)

def endpointA : IntegerEndpointWitness 186 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree186.table
  base := (-1199490156085195445012332801813876514757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13738607510660304951433108110000000000000)
      constant := (312570689200353163137297633468872246970486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 186 interval.damping) (curvature.centralUpper 186 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree186.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 186 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree186.table
  base := (-599745078155286363127625135124674235271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-173173488367163497770109812189000000000000)
      constant := (4055825535732132774388161538787690962471721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 186 interval.damping) (curvature.centralUpper 186 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree186.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 186 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel187
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374944185584659597449/100000000000000000000)
  centralHi := (7498883711693191949/2000000000000000000)
  directionLo := (375956182528045668477/100000000000000000000)
  directionHi := (187978091264022834239/50000000000000000000)

def endpointA : IntegerEndpointWitness 187 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree187.table
  base := (-2270340384952141288762332731251659191679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13813500695937951066871729275000000000000)
      constant := (316143342653396194740848071014373340808321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 187 interval.damping) (curvature.centralUpper 187 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree187.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 187 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree187.table
  base := (-45406807706959275136199060252165489477/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-348234285003323677649272877736000000000000)
      constant := (8204106054763013586873921242280497275390675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 187 interval.damping) (curvature.centralUpper 187 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree187.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 187 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel188
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375956182528045668477/100000000000000000000)
  centralHi := (187978091264022834239/50000000000000000000)
  directionLo := (376965462686409409011/100000000000000000000)
  directionHi := (94241365671602352253/25000000000000000000)

def endpointA : IntegerEndpointWitness 188 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree188.table
  base := (-535069894977474791986075613045832702937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13888393881215597182310350440000000000000)
      constant := (319736140280582630392813861257816669188252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 188 interval.damping) (curvature.centralUpper 188 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree188.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 188 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree188.table
  base := (-214027958025747448412857044345966876941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-350121593272320359758326131094000000000000)
      constant := (8297081157408884807435592130645638115149455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 188 interval.damping) (curvature.centralUpper 188 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree188.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 188 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel189
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376965462686409409011/100000000000000000000)
  centralHi := (94241365671602352253/25000000000000000000)
  directionLo := (11811626494476358809/3125000000000000000)
  directionHi := (377972047823243481889/100000000000000000000)

def endpointA : IntegerEndpointWitness 189 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree189.table
  base := (-1004398957344311704160880844028619732257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-13963287066493243297748971605000000000000)
      constant := (323349082064267511212443817277567760535486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 189 interval.damping) (curvature.centralUpper 189 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree189.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 189 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree189.table
  base := (-1004398957496912120793860889698486471383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35000000000000000000000000000000000000000
      center := (52)
      previous := (18)
      next := (0)
      square := (524252296943522808070348155000000000000)
      linear := (-50286985934473863123911340636000000000000)
      constant := (1198653768424228231226694600497910594700319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 189 interval.damping) (curvature.centralUpper 189 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree189.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 189 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel190
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11811626494476358809/3125000000000000000)
  centralHi := (377972047823243481889/100000000000000000000)
  directionLo := (75795191882602630171/20000000000000000000)
  directionHi := (47371994926626643857/12500000000000000000)

def endpointA : IntegerEndpointWitness 190 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree190.table
  base := (-75035816268292457361736701697374764209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2807636050354177882637518554000000000000)
      constant := (65396433597406367955117846394013126178955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 190 interval.damping) (curvature.centralUpper 190 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree190.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 190 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree190.table
  base := (-468973851743824178145239025140603647279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-176948104905156861988216318905000000000000)
      constant := (4242295859509202035042294754168110421283329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 190 interval.damping) (curvature.centralUpper 190 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree190.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 190 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel191
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75795191882602630171/20000000000000000000)
  centralHi := (47371994926626643857/12500000000000000000)
  directionLo := (189988609323250827033/50000000000000000000)
  directionHi := (379977218646501654067/100000000000000000000)

def endpointA : IntegerEndpointWitness 191 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree191.table
  base := (-435393018290759974567171117714850320689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14113073437048535528626213935000000000000)
      constant := (330635398031678539429090690879765598717244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 191 interval.damping) (curvature.centralUpper 191 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree191.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 191 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree191.table
  base := (-1741572073398341411652415204889497116327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-711567036158620812170971782336000000000000)
      constant := (17158254354267982297644885142297614641299977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 191 interval.damping) (curvature.centralUpper 191 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree191.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 191 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel192
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189988609323250827033/50000000000000000000)
  centralHi := (379977218646501654067/100000000000000000000)
  directionLo := (95243961609007285137/25000000000000000000)
  directionHi := (380975846436029140549/100000000000000000000)

def endpointA : IntegerEndpointWitness 192 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree192.table
  base := (-200728491379363885105565354847970653479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14187966622326181644064835100000000000000)
      constant := (334308772181228507893101233641216234772168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 192 interval.damping) (curvature.centralUpper 192 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree192.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 192 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree192.table
  base := (-80291396562075479658498843732349069003/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-178835413174153544097269572263000000000000)
      constant := (4337091376450192174534204193128774478094265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 192 interval.damping) (curvature.centralUpper 192 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree192.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 192 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel193
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95243961609007285137/25000000000000000000)
  centralHi := (380975846436029140549/100000000000000000000)
  directionLo := (95492965855137201461/25000000000000000000)
  directionHi := (76394372684109761169/20000000000000000000)

def endpointA : IntegerEndpointWitness 193 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree193.table
  base := (-183582874635988487353783824681634114461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14262859807603827759503456265000000000000)
      constant := (338002290418916762250561522303171927084312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 193 interval.damping) (curvature.centralUpper 193 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree193.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 193 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree193.table
  base := (-183582874658662505092418581933333005403/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-179779067308651885151796198942000000000000)
      constant := (4384879222953426725312073559397233365470506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 193 interval.damping) (curvature.centralUpper 193 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree193.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 193 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel194
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/25000000000000000000)
  centralHi := (76394372684109761169/20000000000000000000)
  directionLo := (38296528997062374003/10000000000000000000)
  directionHi := (382965289970623740031/100000000000000000000)

def endpointA : IntegerEndpointWitness 194 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree194.table
  base := (-665038643938330150392873542835990400983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14337752992881473874942077430000000000000)
      constant := (341715952728188672552911737526828019198034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 194 interval.damping) (curvature.centralUpper 194 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree194.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 194 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree194.table
  base := (-1330077288035917355346013700062161717431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-722890885772600904825291302484000000000000)
      constant := (17731708511495640881531028863036154075845881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 194 interval.damping) (curvature.centralUpper 194 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree194.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 194 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel195
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38296528997062374003/10000000000000000000)
  centralHi := (382965289970623740031/100000000000000000000)
  directionLo := (383956146193287883211/100000000000000000000)
  directionHi := (95989036548321970803/25000000000000000000)

def endpointA : IntegerEndpointWitness 195 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree195.table
  base := (-1190070819749125694856145602693282457609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14412646178159119990380698595000000000000)
      constant := (345449759092696281392006686012931717542391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 195 interval.damping) (curvature.centralUpper 195 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree195.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 195 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree195.table
  base := (-1190070819888945257731618965689938639707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-726665502310594269043397809200000000000000)
      constant := (17924940364045539036668679947951193006654357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 195 interval.damping) (curvature.centralUpper 195 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree195.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 195 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel196
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383956146193287883211/100000000000000000000)
  centralHi := (95989036548321970803/25000000000000000000)
  directionLo := (384944451936794369921/100000000000000000000)
  directionHi := (192472225968397184961/50000000000000000000)

def endpointA : IntegerEndpointWitness 196 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree196.table
  base := (-1048643608850185948168212016133615713711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14487539363436766105819319760000000000000)
      constant := (349203709496294706900719621893866384286289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 196 interval.damping) (curvature.centralUpper 196 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree196.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 196 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree196.table
  base := (-65540225560808582761594844644960349851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17500000000000000000000000000000000000000
      center := (26)
      previous := (9)
      next := (0)
      square := (262126148471761404035174077500000000000)
      linear := (-26087147101735272616482296997000000000000)
      constant := (647114730309725651479395328296341110204172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 196 interval.damping) (curvature.centralUpper 196 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree196.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 196 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel197
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384944451936794369921/100000000000000000000)
  centralHi := (192472225968397184961/50000000000000000000)
  directionLo := (385930226795254434657/100000000000000000000)
  directionHi := (192965113397627217329/50000000000000000000)

def endpointA : IntegerEndpointWitness 197 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree197.table
  base := (-226448917781290847465483055464262503381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14562432548714412221257940925000000000000)
      constant := (352977803923038626749910559273767949986476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 197 interval.damping) (curvature.centralUpper 197 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree197.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 197 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree197.table
  base := (-905795671232927483990960444558084885259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (728)
      previous := (252)
      next := (0)
      square := (7339532157209319312984874170000000000000)
      linear := (-734214735386580997479610822632000000000000)
      constant := (18314524764594671833259317292243453840622309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 197 interval.damping) (curvature.centralUpper 197 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree197.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 197 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel198
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385930226795254434657/100000000000000000000)
  centralHi := (192965113397627217329/50000000000000000000)
  directionLo := (386913490113169945683/100000000000000000000)
  directionHi := (96728372528292486421/25000000000000000000)

def endpointA : IntegerEndpointWitness 198 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree198.table
  base := (-152305404464651630338968452774322209759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2000000000000000000000000000000000000000
      center := (3)
      previous := (1)
      next := (0)
      square := (29957274111058446175448466000000000000)
      linear := (-2927465146798411667339312418000000000000)
      constant := (71354408471435768161564392421725677790241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 198 interval.damping) (curvature.centralUpper 198 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree198.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 198 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree198.table
  base := (-190381755604465630229004554142068524801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 122500000000000000000000000000000000000000
      center := (182)
      previous := (63)
      next := (0)
      square := (1834883039302329828246218542500000000000)
      linear := (-184497337981143590424429332337000000000000)
      constant := (4627719327760225354943197198810238642284751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 198 interval.damping) (curvature.centralUpper 198 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree198.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 198 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell428.Kernel199
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386913490113169945683/100000000000000000000)
  centralHi := (96728372528292486421/25000000000000000000)
  directionLo := (96973565247465633293/25000000000000000000)
  directionHi := (387894260989862533173/100000000000000000000)

def endpointA : IntegerEndpointWitness 199 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree199.table
  base := (-615837678000909087856212559295062202881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (15)
      previous := (5)
      next := (0)
      square := (149786370555292230877242330000000000000)
      linear := (-14712218919269704452135183255000000000000)
      constant := (360586424783158910220264559981329937797119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 199 interval.damping) (curvature.centralUpper 199 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree199.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 199 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree199.table
  base := (-307918839041979369935364090472927235623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 245000000000000000000000000000000000000000
      center := (364)
      previous := (126)
      next := (0)
      square := (3669766078604659656492437085000000000000)
      linear := (-370881984231283862957911918032000000000000)
      constant := (9354135043624376201011445935555426565454473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 199 interval.damping) (curvature.centralUpper 199 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree199.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 199 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell428.Kernel199
