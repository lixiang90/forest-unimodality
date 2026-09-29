import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell192.Parameters
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31933_60208.Batch150_199
import ForestUnimodality.BinomialMassData.Q113_213.Batch000_049
import ForestUnimodality.BinomialMassData.Q113_213.Batch050_099
import ForestUnimodality.BinomialMassData.Q113_213.Batch100_149
import ForestUnimodality.BinomialMassData.Q113_213.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree000.table
  base := (739337682838842819477065401/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (357759269280200006835279680000000000000)
      linear := (-26550696277601068366613912500000000000)
      constant := (369668841419421409738532700500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree000.table
  base := (739337682838842819477065401/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (74)
      previous := (37)
      next := (37)
      square := (357759269280200006835279680000000000000)
      linear := (-26550696277601068366613912500000000000)
      constant := (369668841419421409738532700500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree001.table
  base := (101000537339975754468509062808122083611147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-5749680039472798382296022008586052500000000000)
      constant := (2861993808698388534568888076296139166100693607686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree001.table
  base := (403914945731104973908679682778517655022141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-36852788488057501599523199664105000000000000)
      constant := (18335631726510790469266479960966332490699515029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49906787853214316469/100000000000000000000)
  directionHi := (4990678785321431647/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree002.table
  base := (117805966046010769043426623828140890638657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-11123397732587094721940237058420892500000000000)
      constant := (1674251396282532864689009013305801595691401053033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree002.table
  base := (29440581774590801000346941210411291445859/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-35648209948639018728798293067892500000000000)
      constant := (5362310027980806858117112308556204526428707884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/100000000000000000000)
  centralHi := (4990678785321431647/10000000000000000000)
  directionLo := (70578856236492527093/100000000000000000000)
  directionHi := (35289428118246263547/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree003.table
  base := (74087668625907390203028239476665655787521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-16497115425701391061584452108255732500000000000)
      constant := (1062517573001159452619080040641078288853375451049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree003.table
  base := (148107774912674800022045777045495907288447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-11748894589610952590629996956385000000000000)
      constant := (756173782026141801428702821394159868641061327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/100000000000000000000)
  centralHi := (35289428118246263547/50000000000000000000)
  directionLo := (86441092204328492787/100000000000000000000)
  directionHi := (21610273051082123197/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree004.table
  base := (3141494480298507309353858217037695322129/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-21870833118815687401228667158090572500000000000)
      constant := (735343906844822088730084203228935988984697276816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree004.table
  base := (100479238117385392311581461631524145644601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-140183682715719109173743359079145000000000000)
      constant := (4709938243319346469093217534325758963749902769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86441092204328492787/100000000000000000000)
  centralHi := (21610273051082123197/25000000000000000000)
  directionLo := (49906787853214316469/50000000000000000000)
  directionHi := (99813575706428632939/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree005.table
  base := (36429699672304406721753994515376462975857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-27244550811929983740872882207925412500000000000)
      constant := (552473986876847167530453424158410904204128039833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree005.table
  base := (18206173024773536044503964487553138587809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-87313657062469822515908372775412500000000000)
      constant := (1769392674201400861360773036819409189180613042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49906787853214316469/50000000000000000000)
  centralHi := (99813575706428632939/100000000000000000000)
  directionLo := (4463798807137920317/4000000000000000000)
  directionHi := (55797485089224003963/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree006.table
  base := (55553340912059682389708649871976859005411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-65236537010088560161034194515520505000000000000)
      constant := (891641185376732918794537814615164118230791674459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree006.table
  base := (13881966562123899893362522225768355091039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-11615052529675565604993896223472500000000000)
      constant := (158656931789559041017010380855851556027855198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/4000000000000000000)
  centralHi := (55797485089224003963/50000000000000000000)
  directionLo := (122246164941704573117/100000000000000000000)
  directionHi := (61123082470852286559/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree007.table
  base := (21937759022308858215874420936862119613449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-37991986198158576420161312307595092500000000000)
      constant := (381865683652199818480796427299756686705902512881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree007.table
  base := (8771204333065499741068456272183704053713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-243514576943380716747963518494185000000000000)
      constant := (2446336883581131051319307637627147346064525485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122246164941704573117/100000000000000000000)
  centralHi := (61123082470852286559/50000000000000000000)
  directionLo := (6602047469683208113/5000000000000000000)
  directionHi := (132040949393664162261/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree008.table
  base := (35443616337767315756392920892068243411073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-86731407782545745519611054714859865000000000000)
      constant := (687484544957619233070286810368005433733930151337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree008.table
  base := (35428047727184596503910335122507903053113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-277958208352601252606036904965865000000000000)
      constant := (2202293074682103098189964316274221053616683697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6602047469683208113/5000000000000000000)
  centralHi := (132040949393664162261/100000000000000000000)
  directionLo := (70578856236492527093/50000000000000000000)
  directionHi := (141157712472985054187/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree009.table
  base := (29018640986551830455616597026945247767191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-97478843168774338198899484814529545000000000000)
      constant := (645356342508083506749161280830746275567797215279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree009.table
  base := (29005769736408381251584143708398451380363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-34711315529091309829345587937505000000000000)
      constant := (229724288628545540089302081164521593408409883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70578856236492527093/50000000000000000000)
  centralHi := (141157712472985054187/100000000000000000000)
  directionLo := (4678761361238842169/3125000000000000000)
  directionHi := (149720363559642949409/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree010.table
  base := (4785140313539693027631348986200484875977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-108226278555002930878187914914199225000000000000)
      constant := (627790197505768142155509287601036153003891800565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree010.table
  base := (23914799220005946656117760339801097618213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-346845471171042324322183677909225000000000000)
      constant := (2011417121874336173587664520839685997840705597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/3125000000000000000)
  centralHi := (149720363559642949409/100000000000000000000)
  directionLo := (39454780079745565941/25000000000000000000)
  directionHi := (31563824063796452753/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree011.table
  base := (9887360217943583585806670041068467129161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-59486856970615761778738172506934452500000000000)
      constant := (314631272284909567462825803920877315276114588209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree011.table
  base := (494133690096222045139505180301563789229/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-190644551290131430090128532190452500000000000)
      constant := (1008152164757375080939202577665940451070610020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39454780079745565941/25000000000000000000)
  centralHi := (31563824063796452753/20000000000000000000)
  directionLo := (82761044900489174029/50000000000000000000)
  directionHi := (165522089800978348059/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree012.table
  base := (16324432185654781752123717538256096697799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-129721149327460116236764775113538585000000000000)
      constant := (646357024785024689763731053182494135771175768031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree012.table
  base := (16316310000110502019800698901013550088933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-46192525998831488448703383428065000000000000)
      constant := (230137948102482552046808030005349305998311253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/50000000000000000000)
  centralHi := (165522089800978348059/100000000000000000000)
  directionLo := (6915287376346279423/4000000000000000000)
  directionHi := (21610273051082123197/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree013.table
  base := (1341511174230513376054813742197590887769/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-70234292356844354458026602606604132500000000000)
      constant := (338405952050074671664566886171728955412095364805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree013.table
  base := (13408049005202851624122106938943701859769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-450176365398703931896403837324265000000000000)
      constant := (2168986142733732632212746603536921809675859761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/4000000000000000000)
  centralHi := (21610273051082123197/12500000000000000000)
  directionLo := (44985370649616901703/25000000000000000000)
  directionHi := (179941482598467606813/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree014.table
  base := (1366810224043784795552053767917734099011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-75608010049958650797670817656438972500000000000)
      constant := (359518658390668908665702738236114780818733971436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree014.table
  base := (10928335564313279048857580298655415399059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-484619996807924467754477223795945000000000000)
      constant := (2304446438961123964187705411545287541239907771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44985370649616901703/25000000000000000000)
  centralHi := (179941482598467606813/100000000000000000000)
  directionLo := (466835253552848399/250000000000000000)
  directionHi := (186734101421139359601/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree015.table
  base := (4399903465436137548694447935147355671907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-80981727743072947137315032706273812500000000000)
      constant := (385930857756334321817618602268789053248561672283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree015.table
  base := (8794461987161399112995715841804971784931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-57673736468571667068061178918625000000000000)
      constant := (274874450711576241007649149454413862767837171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/250000000000000000)
  centralHi := (186734101421139359601/100000000000000000000)
  directionLo := (9664407910910282537/5000000000000000000)
  directionHi := (193288158218205650741/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree016.table
  base := (6948017372863164150016896609535599994369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-172710890872374486953918495512217305000000000000)
      constant := (834392021479635444993628445734571322436664088361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree016.table
  base := (6943375815032985291465103162086086057929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-553507259626365539470623996739305000000000000)
      constant := (2674396368063513503640192585446523638362180801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9664407910910282537/5000000000000000000)
  centralHi := (193288158218205650741/100000000000000000000)
  directionLo := (199627151412857265877/100000000000000000000)
  directionHi := (99813575706428632939/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree017.table
  base := (2664959528833656160493793739165156536753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-91729163129301539816603462805943492500000000000)
      constant := (452965819234779102236989147326453695940627191257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree017.table
  base := (2662947581145133944155159304439716311423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-293975445517793037664348691605492500000000000)
      constant := (1451897020484802997282977258505367989332950087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199627151412857265877/100000000000000000000)
  centralHi := (99813575706428632939/50000000000000000000)
  directionLo := (205770957754095076591/100000000000000000000)
  directionHi := (12860684859630942287/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree018.table
  base := (1953281211266443532329641328104493991397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-97102880822415836156247677855778332500000000000)
      constant := (492964517045697434085150133314914700515166066093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree018.table
  base := (1951540036010171070079251577730191933639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-34577473469155922843709487204592500000000000)
      constant := (175572022678737892535370272144382897537474199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/100000000000000000000)
  centralHi := (12860684859630942287/6250000000000000000)
  directionLo := (211736568709477581279/100000000000000000000)
  directionHi := (1323353554434234883/625000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree019.table
  base := (330851314856711456451750403758099767839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-102476598515530132495891892905613172500000000000)
      constant := (536971651945368687973394254308654185232094019164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree019.table
  base := (2643801839016213570242833485338148514983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-656838153854027147044844156154345000000000000)
      constant := (3442491191580005584435889723165121459976263727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211736568709477581279/100000000000000000000)
  centralHi := (1323353554434234883/625000000000000000)
  directionLo := (5438466121222110087/2500000000000000000)
  directionHi := (217538644848884403481/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree020.table
  base := (305123193321035269611005496184538434039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-215700632417288857671072215910896025000000000000)
      constant := (1169619772733430879423976429428687065814937962955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree020.table
  base := (1523020489607906345470598484703708562409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-691281785263247682902917542626025000000000000)
      constant := (3749242352492343417392045780187022553767933921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5438466121222110087/2500000000000000000)
  centralHi := (217538644848884403481/100000000000000000000)
  directionLo := (4463798807137920317/2000000000000000000)
  directionHi := (223189940356896015851/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree021.table
  base := (522745975483264892490082751067989870733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-226448067803517450350360646010565705000000000000)
      constant := (1272671940889428097350245256036646461747367433877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree021.table
  base := (52051000949481337794190797306926260353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-40318078704026012153388384949872500000000000)
      constant := (226646236495082851196344608448113576392197365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4463798807137920317/2000000000000000000)
  centralHi := (223189940356896015851/100000000000000000000)
  directionLo := (28587704128682158857/12500000000000000000)
  directionHi := (228701633029457270857/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree022.table
  base := (-189095302435929072958983644081145678123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-118597751594873021514824538055117692500000000000)
      constant := (691433853449764816208066663275639590296658717213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree022.table
  base := (-95028633975607801783067988152243681049/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-380084524040844377309532157784692500000000000)
      constant := (2216458768370259023244528779827496712868975838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/12500000000000000000)
  centralHi := (228701633029457270857/100000000000000000000)
  directionLo := (57149312565644759/24414062500000000)
  directionHi := (46816716853776186573/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree023.table
  base := (-1190501275707947726471403156281474046409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-247942938575974635708937506209905065000000000000)
      constant := (1500018634297099563527332226730868777496234716879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree023.table
  base := (-1192154971683077039595240794147237483533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-794612679490909290477137702041065000000000000)
      constant := (4808494701476495735800248947855968982609591323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57149312565644759/24414062500000000)
  centralHi := (46816716853776186573/20000000000000000000)
  directionLo := (239344546413725543619/100000000000000000000)
  directionHi := (11967227320686277181/5000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree024.table
  base := (-962504210923036814163056408656317853217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-129345186981101614194112968154787372500000000000)
      constant := (811985738142044253925100952829891277530730086327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree024.table
  base := (-77057141460278281059858240814373272149/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-92117367877792202926134565390305000000000000)
      constant := (578430331535407381145316697862928608377422275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/100000000000000000000)
  centralHi := (11967227320686277181/5000000000000000000)
  directionLo := (48898465976681829247/20000000000000000000)
  directionHi := (61123082470852286559/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree025.table
  base := (-2590526055075118827680821646962205858543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-269437809348431821067514366409244425000000000000)
      constant := (1754601424963997890120545434433428976867741026233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree025.table
  base := (-1295872306191630183848298311739450909971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-431749971154675181096642237492212500000000000)
      constant := (2812326355457327612601691206593755351665525701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/20000000000000000000)
  centralHi := (61123082470852286559/25000000000000000000)
  directionLo := (249533939266071582347/100000000000000000000)
  directionHi := (62383484816517895587/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree026.table
  base := (-3194241705765791069500593632112607834753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-280185244734660413746802796508914105000000000000)
      constant := (1891806703692085856020048607901739145404173446743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree026.table
  base := (-3195286594740370686047743871444503894921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-897943573718570898051357861456105000000000000)
      constant := (6064507979297271783901669270074324302791329151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/100000000000000000000)
  centralHi := (62383484816517895587/25000000000000000000)
  directionLo := (254475685124275166203/100000000000000000000)
  directionHi := (63618921281068791551/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree027.table
  base := (-3742023499324697644001221301045699888603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-290932680120889006426091226608583785000000000000)
      constant := (2035504218820881652602623757395304668166600346093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree027.table
  base := (-3742918939993876848182054140788383794339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-103598578347532381545492360880865000000000000)
      constant := (725019191604821917234719616531100757292737101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254475685124275166203/100000000000000000000)
  centralHi := (63618921281068791551/25000000000000000000)
  directionLo := (129661638306492739181/50000000000000000000)
  directionHi := (259323276612985478363/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree028.table
  base := (-2119333868430530766745084975642600908227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-150840057753558799552689828354126732500000000000)
      constant := (1092813026958051897490056582169777195664952189637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree028.table
  base := (-4239434712124175188957690852972083818657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-966830836537011969767504634399465000000000000)
      constant := (7006429489833305037519624233035969529231350567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129661638306492739181/50000000000000000000)
  centralHi := (259323276612985478363/100000000000000000000)
  directionLo := (264081898787328324521/100000000000000000000)
  directionHi := (132040949393664162261/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree029.table
  base := (-4688098909313374936301400453507625895161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-312427550893346191784668086807923145000000000000)
      constant := (2342116637522824265018926424366321756723243957791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree029.table
  base := (-586094444980203751839496288112670940919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-500637233973116252812789010435572500000000000)
      constant := (3754050177093327306454356571884097428325783556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/100000000000000000000)
  centralHi := (132040949393664162261/50000000000000000000)
  directionLo := (268756277584257483033/100000000000000000000)
  directionHi := (134378138792128741517/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree030.table
  base := (-1273382886353479481787343979521470376969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-161587493139787392231978258453796412500000000000)
      constant := (1252465225685469310552887056544230357229750504478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree030.table
  base := (-1273523381677792306531222843231490934843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-57539894408636280082425078185712500000000000)
      constant := (446113310572163820408574268886415108394912874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/100000000000000000000)
  centralHi := (134378138792128741517/50000000000000000000)
  directionLo := (136675367399151520703/50000000000000000000)
  directionHi := (273350734798303041407/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree031.table
  base := (-109152027161285721486058310826810398329/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-166961210832901688571622473503631252500000000000)
      constant := (1337015086660162394812159356627814040248851059975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree031.table
  base := (-218323286412832243517891561092283197949/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-1070161730764673577341724793814505000000000000)
      constant := (8572127716749666927047470261832020089806295475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/50000000000000000000)
  centralHi := (273350734798303041407/100000000000000000000)
  directionLo := (277869234872444886367/100000000000000000000)
  directionHi := (8683413589763902699/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree032.table
  base := (-578247164627486387222043188207066590861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-172334928526015984911266688553466092500000000000)
      constant := (1424692585345699096689024769781752905395771922455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree032.table
  base := (-2891441439346989409219194884395458981321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-552302681086947056599899090143092500000000000)
      constant := (4567133336082251861732046019142742421476447551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277869234872444886367/100000000000000000000)
  centralHi := (8683413589763902699/3125000000000000000)
  directionLo := (282315424945970108373/100000000000000000000)
  directionHi := (141157712472985054187/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree033.table
  base := (-1517479930726262653196243023849426725309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-177708646219130281250910903603300932500000000000)
      constant := (1515485138216851932577711158030302922001765965558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree033.table
  base := (-6070271364842432233673061444658113524617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-126560999287012738784207951861985000000000000)
      constant := (1079597321731211034004855721105843449722405703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315424945970108373/100000000000000000000)
  centralHi := (141157712472985054187/50000000000000000000)
  directionLo := (286692669310272775609/100000000000000000000)
  directionHi := (28669266931027277561/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree034.table
  base := (-6321407197186558945357516812649621651589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-366164727824489155181110237306271545000000000000)
      constant := (3218764793913508793682047815001597306502440641459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree034.table
  base := (-6321707818803671717850814417046374498487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-1173492624992335184915944953229545000000000000)
      constant := (10318389139183352093010551031213513035378143297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286692669310272775609/100000000000000000000)
  centralHi := (28669266931027277561/10000000000000000000)
  directionLo := (291004079198342443877/100000000000000000000)
  directionHi := (145502039599171221939/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree035.table
  base := (-3269068595540358254921035006506679662661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-188456081605358873930199333702970612500000000000)
      constant := (1706375843360256484056257098132260257754107250291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree035.table
  base := (-653839414635814403348860124747029573669/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-603968128200777860387009169850612500000000000)
      constant := (5470125936854254497598004520652447576361055695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291004079198342443877/100000000000000000000)
  centralHi := (145502039599171221939/50000000000000000000)
  directionLo := (147626269328921352967/50000000000000000000)
  directionHi := (59050507731568541187/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree036.table
  base := (-6721100969134836777909491675122425043257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-387659598596946340539687097505610905000000000000)
      constant := (3612916918381202721191985370176588649447648569567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree036.table
  base := (-6721320564084230035982446171375766474227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-138042209756752917403565747352545000000000000)
      constant := (1286879908224491716841290366298754761203421693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147626269328921352967/50000000000000000000)
  centralHi := (59050507731568541187/20000000000000000000)
  directionLo := (4678761361238842169/1562500000000000000)
  directionHi := (299440727119285898817/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree037.table
  base := (-107361187208803681354042329506916211389/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-199203516991587466609487763802640292500000000000)
      constant := (1909624456832611727965380338300126897736295128288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree037.table
  base := (-85891295252125109668457349373135928543/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-638411759609998396245082556322292500000000000)
      constant := (6121676997072178251901053914506700342317305320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4678761361238842169/1562500000000000000)
  centralHi := (299440727119285898817/100000000000000000000)
  directionLo := (37946392395134296379/12500000000000000000)
  directionHi := (303571139161074371033/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree038.table
  base := (-55910855467244811177664920277783370331/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-409154469369403525898263957704950265000000000000)
      constant := (4031738118626700427563063884737571066965431757625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree038.table
  base := (-873627155633090598853938282175823917201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-655633575314608664174119249558132500000000000)
      constant := (6462262879264875188065858767962915178802031324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37946392395134296379/12500000000000000000)
  centralHi := (303571139161074371033/100000000000000000000)
  directionLo := (38455762735694544411/12500000000000000000)
  directionHi := (307646101885556355289/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree039.table
  base := (-56599049509001009343196413482583559557/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-419901904755632118577552387804619945000000000000)
      constant := (4250376640906207932628323409670760596568914358375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree039.table
  base := (-1768754534108567167211721749380096415033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-74761710113246548011461771421552500000000000)
      constant := (756967178353344626600007859315067367943637294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38455762735694544411/12500000000000000000)
  centralHi := (307646101885556355289/100000000000000000000)
  directionLo := (311667790249816898957/100000000000000000000)
  directionHi := (155833895124908449479/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree040.table
  base := (-1425929911550443735069811966139575061959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-430649340141860711256840817904289625000000000000)
      constant := (4475157955345929201727576245696083635172375444645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree040.table
  base := (-3564883266901324073426698192018610254829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-690077206723829200032192636029812500000000000)
      constant := (7172991734514375252340843314396807671348663099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667790249816898957/100000000000000000000)
  centralHi := (155833895124908449479/50000000000000000000)
  directionLo := (315638240637964527529/100000000000000000000)
  directionHi := (31563824063796452753/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree041.table
  base := (-1788385832765157090951458294434334008763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-220698387764044651968064624001979652500000000000)
      constant := (2353038331405574943233298865905123323785686878106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree041.table
  base := (-1788410809413759312597563835988980295841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-707299022428439467961229329265652500000000000)
      constant := (7543115628999090096705832052528014405915979342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638240637964527529/100000000000000000000)
  centralHi := (31563824063796452753/10000000000000000000)
  directionLo := (31955936291533587571/10000000000000000000)
  directionHi := (319559362915335875711/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree042.table
  base := (-714687824632941590279477813084899063493/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-226072105457158948307708839051814492500000000000)
      constant := (2471564146200779401551831021808827386752486948415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree042.table
  base := (-3573481783020282941067970415564014073429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-80502315348116637321140669166832500000000000)
      constant := (880341015089106742801969670863286805055844411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31955936291533587571/10000000000000000000)
  centralHi := (319559362915335875711/100000000000000000000)
  directionLo := (4042911889589163311/1250000000000000000)
  directionHi := (323432951167133064881/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree043.table
  base := (-3554957977645142617196551781963191841573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-231445823150273244647353054101649332500000000000)
      constant := (2593154569542207940580494846207837866900155094163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree043.table
  base := (-1421997762235423638551701876537612308983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-1483485307675320007638605431474665000000000000)
      constant := (16625692655279340849721397483209760335768751365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4042911889589163311/1250000000000000000)
  centralHi := (323432951167133064881/100000000000000000000)
  directionLo := (327260693292834698533/100000000000000000000)
  directionHi := (163630346646417349267/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree044.table
  base := (-7042873445783206823232924202398104887971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-473639081686775081973994538302968345000000000000)
      constant := (5435616130275236193904381410864852100756604572901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree044.table
  base := (-220091739159299029694615031295438833713/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-758964469542270271748339408973172500000000000)
      constant := (8712442289234013567960738050629985768852398448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327260693292834698533/100000000000000000000)
  centralHi := (163630346646417349267/50000000000000000000)
  directionLo := (82761044900489174029/25000000000000000000)
  directionHi := (331044179601956696117/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree045.table
  base := (-6945930791532293251646336810559046270459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-484386517073003674653282968402638025000000000000)
      constant := (5691046716099653847792988294658415037518980852429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree045.table
  base := (-868247987760345698027946256856461074741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-86242920582986726630819566912112500000000000)
      constant := (1013539215742074914555474045608558818888922476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82761044900489174029/25000000000000000000)
  centralHi := (331044179601956696117/100000000000000000000)
  directionLo := (13391396421413760951/4000000000000000000)
  directionHi := (10462028454229500743/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree046.table
  base := (-1704809383095683483358932330741801372957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-247566976229616133666285699251153852500000000000)
      constant := (2976299389524094363445178799019731178451493700534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree046.table
  base := (-426205179535766700657826192620608081671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-793408100951490807606412795444852500000000000)
      constant := (9541074897850248235214394130668960055541347208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13391396421413760951/4000000000000000000)
  centralHi := (10462028454229500743/3125000000000000000)
  directionLo := (84621075904581847989/25000000000000000000)
  directionHi := (338484303618327391957/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree047.table
  base := (-6662917931858199360401969455602923448907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-505881387845460860011859828601977385000000000000)
      constant := (6220270559528345121532275919803068431131914014717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree047.table
  base := (-1665739158819704296740513352435925661259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-810629916656101075535449488680692500000000000)
      constant := (9970105343266652353905439612374186477348680858) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84621075904581847989/25000000000000000000)
  centralHi := (338484303618327391957/100000000000000000000)
  directionLo := (21383981233570479847/6250000000000000000)
  directionHi := (342143699737127677553/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree048.table
  base := (-404817207092380997624225612990573386717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-258314411615844726345574129350823532500000000000)
      constant := (3247030297230813280949075069675290525997479398616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree048.table
  base := (-404819271801745445633264503626189731591/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-91983525817856815940498464657392500000000000)
      constant := (1156549104202894018756186879701083020504398152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21383981233570479847/6250000000000000000)
  centralHi := (342143699737127677553/100000000000000000000)
  directionLo := (6915287376346279423/2000000000000000000)
  directionHi := (345764368817313971151/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree049.table
  base := (-1565448910095986818375247817154400072959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-263688129308959022685218344400658372500000000000)
      constant := (3386983833297710651905268341292700567215326459858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree049.table
  base := (-391363989710506365317805103513295096071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-845073548065321611393522875152372500000000000)
      constant := (10857582734695901922664984132449725018290838408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6915287376346279423/2000000000000000000)
  centralHi := (345764368817313971151/100000000000000000000)
  directionLo := (174673757486250107643/50000000000000000000)
  directionHi := (349347514972500215287/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree050.table
  base := (-1504287618207573702690809633267786097561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-269061847002073319024862559450493212500000000000)
      constant := (3529995381312215678193946125026973964142871504382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree050.table
  base := (-601717453461632447102402674680996797263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-862295363769931879322559568388212500000000000)
      constant := (11316026113301959711462072563060114281524874765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174673757486250107643/50000000000000000000)
  centralHi := (349347514972500215287/100000000000000000000)
  directionLo := (176447140591231317733/50000000000000000000)
  directionHi := (352894281182462635467/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree051.table
  base := (-2871599706841386997221526204817301599249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-274435564695187615364506774500328052500000000000)
      constant := (3676064519281003218890580972649244844136913886919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree051.table
  base := (-5743219946402348150487306163354734432243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-195448262105453810500354724805345000000000000)
      constant := (2618726827537851444452233809115863783727063037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176447140591231317733/50000000000000000000)
  centralHi := (352894281182462635467/100000000000000000000)
  directionLo := (178202876776100855249/50000000000000000000)
  directionHi := (356405753552201710499/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree052.table
  base := (-1087998426434962337104382271949719981839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-559618564776603823408301979100325785000000000000)
      constant := (7650381791083407123189708527435167206522414146045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree052.table
  base := (-2720004825947262434310519791424847266347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-896738995179152415180632954859892500000000000)
      constant := (12262315441827003807776871177620576104373102957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178202876776100855249/50000000000000000000)
  centralHi := (356405753552201710499/100000000000000000000)
  directionLo := (2879063721575481709/800000000000000000)
  directionHi := (179941482598467606813/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree053.table
  base := (-510757003995010262140138756006728535379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-101524741930016449997791101673192500000000000)
      constant := (1415939557456881475141957122388191501015772305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree053.table
  base := (-15961203085858764167722421113183691427/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-913960810883762683109669648095732500000000000)
      constant := (12750159329326820291993924471101847556583749920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2879063721575481709/800000000000000000)
  centralHi := (179941482598467606813/50000000000000000000)
  directionLo := (36332689979241039161/10000000000000000000)
  directionHi := (363326899792410391611/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree054.table
  base := (-2372983840085351106119929120842822311973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-290556717774530504383439419649832572500000000000)
      constant := (4132614238776526475629687382682755291437991596563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree054.table
  base := (-4745980431991298201652574285244035320891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-206929472575193989119712520295905000000000000)
      constant := (2943955912063189106096898415727794817947388469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36332689979241039161/10000000000000000000)
  centralHi := (363326899792410391611/100000000000000000000)
  directionLo := (45842311853139214919/12500000000000000000)
  directionHi := (366738494825113719353/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree055.table
  base := (-1088803469910661760245456981505449169107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-295930435467644800723083634699667412500000000000)
      constant := (4290910757085920193345305390578287356470320601834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree055.table
  base := (-4355224757295942480331358368176911940107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-1896808884585966437935486069134825000000000000)
      constant := (27510483228049041216248711646006056682189285517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45842311853139214919/12500000000000000000)
  centralHi := (366738494825113719353/100000000000000000000)
  directionLo := (185059322286406111187/50000000000000000000)
  directionHi := (2960949156582497779/800000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree056.table
  base := (-3935332705051424104248591927856940667701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-602608306321518194125455699499004505000000000000)
      constant := (8904527202860788667921763190293842264822380998531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree056.table
  base := (-3935341983121371385733126119182287577417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-1931252515995186973793559455606505000000000000)
      constant := (28544957627343408495444661249360858794900168127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185059322286406111187/50000000000000000000)
  centralHi := (2960949156582497779/800000000000000000)
  directionLo := (466835253552848399/125000000000000000)
  directionHi := (373468202842278719201/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree057.table
  base := (-697268851428618047839759212893372043679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-613355741707746786804744129598674185000000000000)
      constant := (9233345258989936604055060088193545022845649891245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree057.table
  base := (-871588042524982834537530653258086984243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-109205341522467083869535157893232500000000000)
      constant := (1644390305351165270428760871378734467024862074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466835253552848399/125000000000000000)
  centralHi := (373468202842278719201/100000000000000000000)
  directionLo := (376787985487949419617/100000000000000000000)
  directionHi := (188393992743974709809/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree058.table
  base := (-601653066147459199340318980774757622663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-624103177093975379484032559698343865000000000000)
      constant := (9568275444741799618769251149285366175020268449765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree058.table
  base := (-3008272078782860035167069471962361036319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2000139778813628045509706228549865000000000000)
      constant := (30672686074572291229966093717095949642143243289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376787985487949419617/100000000000000000000)
  centralHi := (188393992743974709809/50000000000000000000)
  directionLo := (190039386366282583353/50000000000000000000)
  directionHi := (380078772732565166707/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree059.table
  base := (-2501109963575612602543608785450255562767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-634850612480203972163320989798013545000000000000)
      constant := (9909317561339584685181660671624953325450529172377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree059.table
  base := (-1250557858819398273418466103967008585543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1017291705111424290683889807510772500000000000)
      constant := (15882969363273571948110311176942428287482499633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190039386366282583353/50000000000000000000)
  centralHi := (380078772732565166707/100000000000000000000)
  directionLo := (23958831956781115699/6250000000000000000)
  directionHi := (76668262261699570237/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree060.table
  base := (-982444946498602631623566629582579545311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-322799023933216282421304709948841612500000000000)
      constant := (5128235721290292806824506523978399477307453082441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree060.table
  base := (-61402962468840181557560377981658375921/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-114945946757337173179214055638512500000000000)
      constant := (1826599051159366648658274772121261362031715824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23958831956781115699/6250000000000000000)
  centralHi := (76668262261699570237/20000000000000000000)
  directionLo := (386576316436411301481/100000000000000000000)
  directionHi := (193288158218205650741/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree061.table
  base := (-349903734033827471910956454746070961137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-328172741626330578760948924998676452500000000000)
      constant := (5304868474726268344092691707808115532302365295694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree061.table
  base := (-699809559326062887546430706574747630513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1051735336520644826541963193982452500000000000)
      constant := (17005609106556025974408096307547442774751255703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386576316436411301481/100000000000000000000)
  centralHi := (193288158218205650741/50000000000000000000)
  directionLo := (77956894731221854283/20000000000000000000)
  directionHi := (48723059207013658927/12500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree062.table
  base := (-805293306612935047292465695306249242213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-667092918638889750201186280097022585000000000000)
      constant := (10969113965649148005129050867267115267099141986003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree062.table
  base := (-805296871970124824865657317951744050449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2137914304450510188941999774436585000000000000)
      constant := (35163244231461141786426885511754157324175179319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77956894731221854283/20000000000000000000)
  centralHi := (48723059207013658927/12500000000000000000)
  directionLo := (392966440522846534143/100000000000000000000)
  directionHi := (767512579146184637/195312500000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree063.table
  base := (-181931878479422287116975143532086216421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-677840354025118342880474710196692265000000000000)
      constant := (11334602393832719173865171571630111801315408064851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree063.table
  base := (-181934917429842283242903598193853155213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-241373103984414524977785906767585000000000000)
      constant := (4037206740528201055234080204918419786244571267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392966440522846534143/100000000000000000000)
  centralHi := (767512579146184637/195312500000000000)
  directionLo := (396122848180992486781/100000000000000000000)
  directionHi := (198061424090496243391/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree064.table
  base := (117615898428737821178191540699388083831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-344293894705673467779881570148180972500000000000)
      constant := (5853101076258922875772614375909110096927266254878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree064.table
  base := (1837738295780007566912240588933847827/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1103400783634475630329073273689972500000000000)
      constant := (18763033626257663694529435655513675486984084864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396122848180992486781/100000000000000000000)
  centralHi := (198061424090496243391/50000000000000000000)
  directionLo := (79850860565142906351/20000000000000000000)
  directionHi := (99813575706428632939/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree065.table
  base := (1151888291331410365231436231730515547957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-699335224797575528239051570396031625000000000000)
      constant := (12083913173471788329926207247285981348553698724733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree065.table
  base := (143985760524656850234250782458479691717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1120622599339085898258109966925812500000000000)
      constant := (19368431888322077507753327200206997560534034292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79850860565142906351/20000000000000000000)
  centralHi := (99813575706428632939/25000000000000000000)
  directionLo := (25147586691391816489/6250000000000000000)
  directionHi := (16094455482490762553/4000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree066.table
  base := (14549517018942796153122406311783008931/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-355041330091902060459170000247850652500000000000)
      constant := (6233867699772439855636520352338242720696154037696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree066.table
  base := (116396018609675943487928284979339067299/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-126427157227077351798571851129072500000000000)
      constant := (2220402780804080227065466864333651785906034072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25147586691391816489/6250000000000000000)
  centralHi := (16094455482490762553/4000000000000000000)
  directionLo := (405444661171532560633/100000000000000000000)
  directionHi := (202722330585766280317/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree067.table
  base := (1300904936908296675568393911632595111787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-360415047785016356798814215297685492500000000000)
      constant := (6428834391429532861468678014908037609097727812003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree067.table
  base := (2601808271493135613707649825114985768679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2310132461496612868232366706794985000000000000)
      constant := (41217225932978129565000473427884376789339197551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405444661171532560633/100000000000000000000)
  centralHi := (202722330585766280317/50000000000000000000)
  directionLo := (408504664289558122133/100000000000000000000)
  directionHi := (204252332144779061067/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree068.table
  base := (3370300544243515492533785100998570822587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-731577530956261306276916860695040665000000000000)
      constant := (13253713283294854383924934273714434985356300937203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree068.table
  base := (3370299179216088899935397953496920281681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2344576092905833404090440093266665000000000000)
      constant := (42486791283936519342437887476399261776259585289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408504664289558122133/100000000000000000000)
  centralHi := (204252332144779061067/50000000000000000000)
  directionLo := (205770957754095076591/50000000000000000000)
  directionHi := (411541915508190153183/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree069.table
  base := (2083903907535929832435205711247799960131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-371162483171244949478102645397355172500000000000)
      constant := (6827934433613516411138188004621012608157398222139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree069.table
  base := (2083903326161471126182587091435054807769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-132167762461947441108250748874352500000000000)
      constant := (2431996999993753709862663337931316611285963529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205770957754095076591/50000000000000000000)
  centralHi := (411541915508190153183/100000000000000000000)
  directionLo := (207278457451549980743/50000000000000000000)
  directionHi := (414556914903099961487/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree070.table
  base := (312145605979142106288657473158185166091/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-376536200864359245817746860447190012500000000000)
      constant := (7032067753233934016962483179773027870793633035032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree070.table
  base := (199773148213102419136305978701204070629/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2413463355724274475806586866210025000000000000)
      constant := (45084689990751751402718045977503123187009177525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207278457451549980743/50000000000000000000)
  centralHi := (414556914903099961487/100000000000000000000)
  directionLo := (208775072247503846357/50000000000000000000)
  directionHi := (83510028899001538543/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree071.table
  base := (365616532311521592411918237656708691857/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (207866)
      previous := (103933)
      next := (103933)
      square := (1004945787408081819200300621120000000000000)
      linear := (-75760745597594434072087100872252500000000000)
      constant := (1436075498649418507743209979043617338973410504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree071.table
  base := (5849863673582148546804728945434040086549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1332)
      previous := (666)
      next := (666)
      square := (6439666847043600123035034240000000000000)
      linear := (-485599481676948028499238296505000000000000)
      constant := (9207106364016200635833179261023906360778941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208775072247503846357/50000000000000000000)
  centralHi := (83510028899001538543/20000000000000000000)
  directionLo := (105130517287330615701/25000000000000000000)
  directionHi := (84104413829864492561/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree072.table
  base := (6734410879377846395551583242739906125121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-774567272501175676994070581093719385000000000000)
      constant := (14899001860154485448130159526544126941275848505449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree072.table
  base := (1683602540297183768449384621501174501859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-137908367696817530417929646619632500000000000)
      constant := (2653385861517712206742734208571594841327742438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105130517287330615701/25000000000000000000)
  centralHi := (84104413829864492561/20000000000000000000)
  directionLo := (423473137418955162559/100000000000000000000)
  directionHi := (1323353554434234883/312500000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree073.table
  base := (1529593521783549547975519239501789447197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-785314707887404269673359011193389065000000000000)
      constant := (15325601538157978752551873505294105105311130481465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree073.table
  base := (3823983498709183069496102392176317826727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1258397124975968041690403512812532500000000000)
      constant := (24564228458288203220353086818967589863480777263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423473137418955162559/100000000000000000000)
  centralHi := (1323353554434234883/312500000000000000)
  directionLo := (213201891167315295417/50000000000000000000)
  directionHi := (85280756466926118167/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree074.table
  base := (8590533720840464232905364050869424944549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-796062143273632862352647441293058745000000000000)
      constant := (15758312197449498515740399579576944678522629468781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree074.table
  base := (1073816650029724929384370010952081008967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1275618940680578309619440206048372500000000000)
      constant := (25257778682112280696502705988290684853183295292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213201891167315295417/50000000000000000000)
  centralHi := (85280756466926118167/20000000000000000000)
  directionLo := (85862884429328313397/20000000000000000000)
  directionHi := (214657211073320783493/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree075.table
  base := (2390527097236441266035303297607502868203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-403404789329930727515967935696364212500000000000)
      constant := (8098566913164954920790070178805171982719728412614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree075.table
  base := (9562107945776135599832155389737643627101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-287297945863375239455217088729825000000000000)
      constant := (5769138534765009527233628858719042461524216141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85862884429328313397/20000000000000000000)
  centralHi := (214657211073320783493/50000000000000000000)
  directionLo := (432205461021642463937/100000000000000000000)
  directionHi := (216102730510821231969/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree076.table
  base := (10562690919970623818238954199350933702447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-817557014046090047711224301492398105000000000000)
      constant := (16642066414982491114578329603745840332784445233543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree076.table
  base := (10562690542757364660094249427347052655033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2620125144179597690955027185040105000000000000)
      constant := (53348525231195478200525187976027448431906192177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432205461021642463937/100000000000000000000)
  centralHi := (216102730510821231969/50000000000000000000)
  directionLo := (435077289697768806961/100000000000000000000)
  directionHi := (217538644848884403481/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree077.table
  base := (5796140366062313467017159332274066676459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-414152224716159320195256365796033892500000000000)
      constant := (8546554977584495878064494720246400852049677761571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree077.table
  base := (11592280411085905859022850879219817662067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2654568775588818226813100571511785000000000000)
      constant := (54794392592837382355915995743396908907510317723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435077289697768806961/100000000000000000000)
  centralHi := (217538644848884403481/50000000000000000000)
  directionLo := (437930286101089362979/100000000000000000000)
  directionHi := (21896514305054468149/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree078.table
  base := (2530175467421388498316745451163275476787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-839051884818547233069801161691737465000000000000)
      constant := (17550264439974989463405124314070615174849297485015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree078.table
  base := (6325438531953194689215331533133463814921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-149389578166557709037287442110192500000000000)
      constant := (3125547159762369829888541309308120791091016761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437930286101089362979/100000000000000000000)
  centralHi := (21896514305054468149/5000000000000000000)
  directionLo := (88152963185228827187/20000000000000000000)
  directionHi := (1721737562211500531/390625000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree079.table
  base := (549539213001473290287573809876994509083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-849799320204775825749089591791407145000000000000)
      constant := (18013529863596503713172811389821783840579682875675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree079.table
  base := (13738480092570728450281738553490352732403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2723456038407259298529247344455145000000000000)
      constant := (57744894061311346898179408549296818813116391707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88152963185228827187/20000000000000000000)
  centralHi := (1721737562211500531/390625000000000000)
  directionLo := (221790616591546464469/50000000000000000000)
  directionHi := (443581233183092928939/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree080.table
  base := (232110771122235164325326577214487812567/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-430273377795502209214189010945538412500000000000)
      constant := (9241453110580572157350428174706479231080449402336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree080.table
  base := (14855089154038736099331782689983495488213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2757899669816479834387320730926825000000000000)
      constant := (59249528134040061993593132284631861206804735597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221790616591546464469/50000000000000000000)
  centralHi := (443581233183092928939/100000000000000000000)
  directionLo := (446379880713792031701/100000000000000000000)
  directionHi := (223189940356896015851/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree081.table
  base := (16000704128575346393005751900116333135159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-871294190977233011107666451990746505000000000000)
      constant := (18958393508578176493111848283015649897791651281871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree081.table
  base := (1600070396031628155252711993077295469789/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-155130183401427798346966339855472500000000000)
      constant := (3376319504491266472510680142652855732316031745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446379880713792031701/100000000000000000000)
  centralHi := (223189940356896015851/50000000000000000000)
  directionLo := (17966443627157153929/4000000000000000000)
  directionHi := (224580545339464424113/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree082.table
  base := (1073457775795391907208105714221576824693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-441020813181730801893477441045208092500000000000)
      constant := (9719995861206402085710889211917070816210590024936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree082.table
  base := (8587662134799926186533873913654442096609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1413393466317460453051733751935092500000000000)
      constant := (31158781445374583438615780043783593383481053721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17966443627157153929/4000000000000000000)
  centralHi := (224580545339464424113/50000000000000000000)
  directionLo := (112981296254543467329/25000000000000000000)
  directionHi := (451925185018173869317/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree083.table
  base := (9189475000292869315377662695380590539767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-446394530874845098233121656095042932500000000000)
      constant := (9963850429890370666491699253810983265269151940623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree083.table
  base := (2297368734856317921112013009011640865381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1430615282022070720980770445170932500000000000)
      constant := (31940481777273750510026312649875164037685882356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112981296254543467329/25000000000000000000)
  centralHi := (451925185018173869317/100000000000000000000)
  directionLo := (90934495177030905107/20000000000000000000)
  directionHi := (14208514871411078923/3125000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree084.table
  base := (19611580721096114966214732145670453328131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-903536497135918789145531742289755545000000000000)
      constant := (20421520918259782946509621115419999446182947414139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree084.table
  base := (19611580617565720871415967007210777954401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-321741577272595775313290475201505000000000000)
      constant := (7273772562722473882971655135989209531668135441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90934495177030905107/20000000000000000000)
  centralHi := (14208514871411078923/3125000000000000000)
  directionLo := (28587704128682158857/6250000000000000000)
  directionHi := (457403266058914541713/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree085.table
  base := (20873216430593435224107243742994898569389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-914283932522147381824820172389425225000000000000)
      constant := (20921451895815622998336454494553578384567906466741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree085.table
  base := (10436608171277198686957489303258159385889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1465058913431291256838843831642612500000000000)
      constant := (33533265707058513372558169944368331933178398041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28587704128682158857/6250000000000000000)
  centralHi := (457403266058914541713/100000000000000000000)
  directionLo := (115029462333348511471/25000000000000000000)
  directionHi := (92023569866678809177/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree086.table
  base := (2770482126051503824768869504607307890611/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-462515683954187987252054301244547452500000000000)
      constant := (10713746895369807612834459310337648886276841093036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree086.table
  base := (22163856933553932614862072282366627189329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-2964561458271803049535761049756905000000000000)
      constant := (68688698597935590689141553334236881508952667401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115029462333348511471/25000000000000000000)
  centralHi := (92023569866678809177/20000000000000000000)
  directionLo := (18512660435453944497/4000000000000000000)
  directionHi := (231408255443174306213/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree087.table
  base := (23483502353196269852956197693155824434703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-935778803294604567183397032588764585000000000000)
      constant := (21939646601596546761112216966839770778892223944807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree087.table
  base := (23483502289552081210093190949696911115171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-333222787742335953932648270692065000000000000)
      constant := (7814494956819459135331821939390137128931577011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18512660435453944497/4000000000000000000)
  centralHi := (231408255443174306213/50000000000000000000)
  directionLo := (465499527629018527793/100000000000000000000)
  directionHi := (232749763814509263897/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree088.table
  base := (12416076189902631772137700183131252935369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-473263119340416579931342731344217132500000000000)
      constant := (11228955163590404110662743943716952201996571117361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree088.table
  base := (4966430465140097967063081956610863959557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3033448721090244121251907822700265000000000000)
      constant := (71991799450586166389681026543153751434905707665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465499527629018527793/100000000000000000000)
  centralHi := (232749763814509263897/50000000000000000000)
  directionLo := (468167168537761865729/100000000000000000000)
  directionHi := (46816716853776186573/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree089.table
  base := (13104903508357443446108409582562294401267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-478636837033530876270986946394051972500000000000)
      constant := (11491142483239802955924188236547744285968444534123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree089.table
  base := (2620980697072422167208129327071926024927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1533946176249732328554990604585972500000000000)
      constant := (36836366556167510297854649449216613559124565315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468167168537761865729/100000000000000000000)
  centralHi := (46816716853776186573/10000000000000000000)
  directionLo := (58852461871096945191/12500000000000000000)
  directionHi := (470819694968775561529/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree090.table
  base := (6904116550959242676611183640443415925799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-484010554726645172610631161443886812500000000000)
      constant := (11756385259321040601022567884285945188580710600062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree090.table
  base := (13808233082373673237824253816096280963097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-172351999106038066276003033091312500000000000)
      constant := (4187403088550287986488749976614566352334971977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58852461871096945191/12500000000000000000)
  centralHi := (470819694968775561529/100000000000000000000)
  directionLo := (473457360956946791293/100000000000000000000)
  directionHi := (236728680478473395647/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree091.table
  base := (29052129890688479244078069883939775327351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-978768544839518937900550752987443305000000000000)
      constant := (24049366982953385774163529181281809639769820482319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree091.table
  base := (7263032464366894137515518652296934191533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1568389807658952864413063991057652500000000000)
      constant := (38546683446507245691233923588220226714671321354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473457360956946791293/100000000000000000000)
  centralHi := (236728680478473395647/50000000000000000000)
  directionLo := (119020103374950470983/25000000000000000000)
  directionHi := (476080413499801883933/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree092.table
  base := (30516798034854353828868169127673696633701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-989515980225747530579839183087112985000000000000)
      constant := (24592074358812915229202959456186460637437937255469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree092.table
  base := (122067192026495061262188645775695584473/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1585611623363563132342100684293492500000000000)
      constant := (39416533503872798756771268651590121621494442125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119020103374950470983/25000000000000000000)
  centralHi := (476080413499801883933/100000000000000000000)
  directionLo := (239344546413725543619/50000000000000000000)
  directionHi := (478689092827451087239/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree093.table
  base := (32010470600696796870112479101120385911789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1000263415611976123259127613186782665000000000000)
      constant := (25140892645716032330491285611357686556043651332341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree093.table
  base := (8002617644177290210068677766858833696289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-178092604340908155585681930836592500000000000)
      constant := (4477353107582644240090356526062203261325985698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239344546413725543619/50000000000000000000)
  centralHi := (478689092827451087239/100000000000000000000)
  directionLo := (60160454082420525723/12500000000000000000)
  directionHi := (96256726531872841157/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree094.table
  base := (83832868895678477409711768437745691869/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-505505425499102357969208021643226172500000000000)
      constant := (12847910921619359533491185041227427941739893172200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree094.table
  base := (33533147537890909557878144172728969599863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3240110509545567336400348141530345000000000000)
      constant := (82371233677887001073267002337679730621776184447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60160454082420525723/12500000000000000000)
  centralHi := (96256726531872841157/20000000000000000000)
  directionLo := (483864260448753916871/100000000000000000000)
  directionHi := (60483032556094239609/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree095.table
  base := (35084828882416832897808557986142216028851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1021758286384433308617704473386122025000000000000)
      constant := (26256861951024687132928721627041284226065539035819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree095.table
  base := (35084828865102675838984367279184842351079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3274554140954787872258421528002025000000000000)
      constant := (84169700230806577187295264030738212112626103151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483864260448753916871/100000000000000000000)
  centralHi := (60483032556094239609/12500000000000000000)
  directionLo := (3800243731369453063/781250000000000000)
  directionHi := (97286239523057998413/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree096.table
  base := (36665514551990413867267580075408158547061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1032505721770661901296992903485791705000000000000)
      constant := (26824012968774552198539183320775544759005178213309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree096.table
  base := (9166378634320645504886633496053863643513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-183833209575778244895360828581872500000000000)
      constant := (4777097533016153796442836731880895053253898066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3800243731369453063/781250000000000000)
  centralHi := (97286239523057998413/20000000000000000000)
  directionLo := (48898465976681829247/10000000000000000000)
  directionHi := (488984659766818292471/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree097.table
  base := (9568801137306465816608822406418802190367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-521626578578445246988140666792730692500000000000)
      constant := (13698637448118370434767759882648995345555083784046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree097.table
  base := (38275204536733148820996856203872898255069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3343441403773228943974568300945385000000000000)
      constant := (87825399767536657581905051789452794520934225461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48898465976681829247/10000000000000000000)
  centralHi := (488984659766818292471/100000000000000000000)
  directionLo := (245762428455356446571/50000000000000000000)
  directionHi := (491524856910712893143/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree098.table
  base := (9978474714798483675069849318709552598681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-527000296271559543327784881842565532500000000000)
      constant := (13988323866599926246960716491392155406860924274178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree098.table
  base := (19956949424291834109968147829500744206961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1688942517591224739916320843708532500000000000)
      constant := (44841316374934787886391822454920624263925613609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245762428455356446571/50000000000000000000)
  centralHi := (491524856910712893143/100000000000000000000)
  directionLo := (494051993655447689653/100000000000000000000)
  directionHi := (247025996827723844827/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree099.table
  base := (2598849841834329189017830915633213261629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-532374013964673839667429096892400372500000000000)
      constant := (14281065739743121318862281347853663545787912842408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree099.table
  base := (41581597460338587161617665953165201345447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-379147629621296668410079452654305000000000000)
      constant := (10173272726746956906896223937266840779982398327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494051993655447689653/100000000000000000000)
  centralHi := (247025996827723844827/50000000000000000000)
  directionLo := (19862650776117401767/4000000000000000000)
  directionHi := (31035391837683440261/6250000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree100.table
  base := (43278300369149698693632167154040054166097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1075495463315576272014146623884470425000000000000)
      constant := (29153726134946632511844945094648563543511087590393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree100.table
  base := (1731132014459924772168172533973855133651/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3446772298000890551548788460360425000000000000)
      constant := (93455865139619401943209376222738995838965305475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19862650776117401767/4000000000000000000)
  centralHi := (31035391837683440261/6250000000000000000)
  directionLo := (249533939266071582347/50000000000000000000)
  directionHi := (99813575706428632939/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree101.table
  base := (22502003774868216438794393120305858419941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-543121449350902432346717526992070052500000000000)
      constant := (14875715849727790028011380794909854821760187530029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree101.table
  base := (45004007543239515448284229311053504886951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3481215929410111087406861846832105000000000000)
      constant := (95371864546159665807785603856561451463216079919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249533939266071582347/50000000000000000000)
  centralHi := (99813575706428632939/20000000000000000000)
  directionLo := (125389252643617682661/25000000000000000000)
  directionHi := (100311402114894146129/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree102.table
  base := (46758719003665312637373359503470411937807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1096990334088033457372723484083809785000000000000)
      constant := (30355248172907674749942339346623564720163964609383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree102.table
  base := (46758718998149280275812981430489388020969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-390628840091036847029437248144865000000000000)
      constant := (10811939195556340098523371164773287005013704729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125389252643617682661/25000000000000000000)
  centralHi := (100311402114894146129/20000000000000000000)
  directionLo := (12600846259533163899/2500000000000000000)
  directionHi := (504033850381326555961/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree103.table
  base := (12135608681170256932603195866427207987673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-553868884737131025026005957091739732500000000000)
      constant := (15482587777607170171710706112486316850888449193474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree103.table
  base := (1213560867999954528173580258973566385867/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1775051596114276079561504309887732500000000000)
      constant := (49631314890439486561719485627820852167207998460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12600846259533163899/2500000000000000000)
  centralHi := (504033850381326555961/100000000000000000000)
  directionLo := (126624644571083403003/25000000000000000000)
  directionHi := (506498578284333612013/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree104.table
  base := (6294394338440923208101257867555897081901/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-559242602430245321365650172141574572500000000000)
      constant := (15790606923150574131239093821214256017255300005076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree104.table
  base := (25177577351776101026141664298544999818713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1792273411818886347490541003123572500000000000)
      constant := (50618697804268970224181774620675508096775190097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126624644571083403003/25000000000000000000)
  centralHi := (506498578284333612013/100000000000000000000)
  directionLo := (508951370248550332407/100000000000000000000)
  directionHi := (63618921281068791551/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree105.table
  base := (26098439473893940005948749930773437707833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-564616320123359617705294387191409412500000000000)
      constant := (16101681523052780014846572274766852190372637903777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree105.table
  base := (26098439472206846865165889452102381554613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-201055025280388512824397521817712500000000000)
      constant := (5735097235710246994967603904979610605416804133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508951370248550332407/100000000000000000000)
  centralHi := (63618921281068791551/12500000000000000000)
  directionLo := (511392398019077620791/100000000000000000000)
  directionHi := (63924049752384702599/12500000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree106.table
  base := (3379225465109482040778396160156789151447/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-202915641800097513009946102613472500000000000)
      constant := (5844005545492173392056467585927887680399554616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree106.table
  base := (54067607438887890919780243060182651763121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3653434086456213766697228779190505000000000000)
      constant := (105245693683450861702366017311159716727841036649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511392398019077620791/100000000000000000000)
  centralHi := (63924049752384702599/12500000000000000000)
  directionLo := (256910914630698613947/50000000000000000000)
  directionHi := (102764365852279445579/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree107.table
  base := (55967340186301202047264303180890987037199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1150727511019176420769165634582158185000000000000)
      constant := (33465994171665411625634976093293226277336047126631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree107.table
  base := (55967340183870742323036579872304623434571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3687877717865434302555302165662185000000000000)
      constant := (107279225930396360123890532452158723460603051699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256910914630698613947/50000000000000000000)
  centralHi := (102764365852279445579/20000000000000000000)
  directionLo := (258119913847883007819/50000000000000000000)
  directionHi := (516239827695766015639/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree108.table
  base := (57896077178817160646618655291236396041327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1161474946405405013448454064681827865000000000000)
      constant := (34106476097339616418531796499303491278146121304263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree108.table
  base := (28948038588377323438373549997936864380313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-206795630515258602134076419562992500000000000)
      constant := (6074019276861257606741506787819469733341157833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258119913847883007819/50000000000000000000)
  centralHi := (516239827695766015639/100000000000000000000)
  directionLo := (20745862129038838269/4000000000000000000)
  directionHi := (259323276612985478363/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree109.table
  base := (59853818417099371193100599627375911115191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1172222381791633606127742494781497545000000000000)
      constant := (34753068931566489047061957791366315785107583027279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree109.table
  base := (14963454603837308879235567481726509421997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1878382490341937687135724469302772500000000000)
      constant := (55702528421335158620336276365696332511933163786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20745862129038838269/4000000000000000000)
  centralHi := (259323276612985478363/50000000000000000000)
  directionLo := (104208432412546282321/20000000000000000000)
  directionHi := (260521081031365705803/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree110.table
  base := (61840563899299750705571562684180202620567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1182969817177862198807030924881167225000000000000)
      constant := (35405772674319860343886513956230146123686471595823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree110.table
  base := (61840563897814795128308763974199519997909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3791208612093095910129522325077225000000000000)
      constant := (113497355507815935137538173830801208022785133421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104208432412546282321/20000000000000000000)
  centralHi := (260521081031365705803/50000000000000000000)
  directionLo := (6542835085525227189/1250000000000000000)
  directionHi := (523426806842018175121/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree111.table
  base := (638563136238661764322846261856949324871/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-596858626282045395743159677490418452500000000000)
      constant := (18032293662788875994265991792939140115261713159950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree111.table
  base := (12771262724521263143404282537722223348653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-425072471500257382887510634616545000000000000)
      constant := (12845471442096599450392681262915323639502798865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6542835085525227189/1250000000000000000)
  centralHi := (523426806842018175121/100000000000000000000)
  directionLo := (525800636738542895373/100000000000000000000)
  directionHi := (262900318369271447687/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree112.table
  base := (3295053379474763591632101173030506770213/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-602232343975159692082803892540253292500000000000)
      constant := (18364756442660853974456433471611200772718602459970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree112.table
  base := (8237633448553308077525390917006025290233/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1930047937455768490922834549010292500000000000)
      constant := (58870359627885919151539177349462865445570323908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525800636738542895373/100000000000000000000)
  centralHi := (262900318369271447687/50000000000000000000)
  directionLo := (264081898787328324521/50000000000000000000)
  directionHi := (528163797574656649043/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree113.table
  base := (33987412897546361297414870580574169986721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-607606061668273988422448107590088132500000000000)
      constant := (18700274676768116274717379451344862649515447115849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree113.table
  base := (6797482579418606266174495715585838355519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-1947269753160378758851871242246132500000000000)
      constant := (59945892169236924958064978420902312001757707555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264081898787328324521/50000000000000000000)
  centralHi := (528163797574656649043/100000000000000000000)
  directionLo := (530516431924882629107/100000000000000000000)
  directionHi := (132629107981220657277/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree114.table
  base := (35038794119869960565725491774205858549921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-612979779361388284762092322639922972500000000000)
      constant := (19038848365104159075707719283279489178794476296649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree114.table
  base := (8759698529871358109178242820484064686747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-218276840984998780753434215053552500000000000)
      constant := (6781246568162997306262540059972245680343566508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530516431924882629107/100000000000000000000)
  centralHi := (132629107981220657277/25000000000000000000)
  directionLo := (266429339608147494313/50000000000000000000)
  directionHi := (532858679216294988627/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree115.table
  base := (36104677461332964946083719264515044296367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-618353497054502581101736537689757812500000000000)
      constant := (19380477507663524074426834714206647609185292806023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree115.table
  base := (72209354922013639678458438688573114002571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3963426769139198589419889257435625000000000000)
      constant := (124252680921117334563458368751837248609182643699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266429339608147494313/50000000000000000000)
  centralHi := (532858679216294988627/100000000000000000000)
  directionLo := (535190675824943819543/100000000000000000000)
  directionHi := (66898834478117977443/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree116.table
  base := (18592531460805978761347445283941238524123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-623727214747616877441380752739592652500000000000)
      constant := (19725162104441631632689614554060329626516784513574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree116.table
  base := (74370125842670701120191490318679738353389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-3997870400548419125277962643907305000000000000)
      constant := (126462512420994795680160602671834521049354905541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535190675824943819543/100000000000000000000)
  centralHi := (66898834478117977443/12500000000000000000)
  directionLo := (268756277584257483033/50000000000000000000)
  directionHi := (537512555168514966067/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree117.table
  base := (38279950500435668762164866633696210629029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-629100932440731173781024967789427492500000000000)
      constant := (20072902155434640528058646650274370519510396945901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree117.table
  base := (76559901000402183712416807210482805511317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-448034892439737740126226225597665000000000000)
      constant := (14299103636282426856176515435491708822582548997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268756277584257483033/50000000000000000000)
  centralHi := (537512555168514966067/100000000000000000000)
  directionLo := (539824447795402820437/100000000000000000000)
  directionHi := (269912223897701410219/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree118.table
  base := (393893401975766511158349243522622691393/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-634474650133845470120669182839262332500000000000)
      constant := (20423697660639330064806287760291298051148472541700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree118.table
  base := (7877868039475546290352598634085807574429/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2033378831683430098497054708425332500000000000)
      constant := (65470470918868968758230277928926850019221346505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539824447795402820437/100000000000000000000)
  centralHi := (269912223897701410219/50000000000000000000)
  directionLo := (542126481470364372243/100000000000000000000)
  directionHi := (135531620367591093061/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree119.table
  base := (40513232012844280907710117289717334286439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-639848367826959766460313397889097172500000000000)
      constant := (20777548620053000979465048199461660311506720648191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree119.table
  base := (20256616006337804859647066531838497612139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2050600647388040366426091401661172500000000000)
      constant := (66604769877282936888749699882442619096330268582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542126481470364372243/100000000000000000000)
  centralHi := (135531620367591093061/25000000000000000000)
  directionLo := (272209390628456766089/50000000000000000000)
  directionHi := (544418781256913532179/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree120.table
  base := (83303251892157751774592764653038885354649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1290444171040148125599915225877864025000000000000)
      constant := (42268910067346784288763263401032151792693454775681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree120.table
  base := (41651625945935862985647013731124608879001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-229758051454738959372792010544112500000000000)
      constant := (7527651470945068639818358307290099153359044041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272209390628456766089/50000000000000000000)
  centralHi := (544418781256913532179/100000000000000000000)
  directionLo := (136675367399151520703/25000000000000000000)
  directionHi := (546701469596606082813/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree121.table
  base := (85609043994293501169443499105960942046631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1301191606426376718279203655977533705000000000000)
      constant := (42988833802997221101419613522340892485217000840639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree121.table
  base := (17121808798810200311366659922586232474071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4170088557594521804568329576265705000000000000)
      constant := (137805502005061955444668621594695438905580635995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136675367399151520703/25000000000000000000)
  centralHi := (546701469596606082813/100000000000000000000)
  directionLo := (137243666596339370291/25000000000000000000)
  directionHi := (109794933277071496233/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree122.table
  base := (8794384033187211994831398080695727815697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-655969520906302655479246043038601692500000000000)
      constant := (21857434223527072453982022139795939351928851863965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree122.table
  base := (43971920165833268096089092475069123886321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2102266094501871170213201481368692500000000000)
      constant := (70066433169353969252493271633882116081598497449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137243666596339370291/25000000000000000000)
  centralHi := (109794933277071496233/20000000000000000000)
  directionLo := (55123848904692811301/10000000000000000000)
  directionHi := (551238489046928113011/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree123.table
  base := (11288455113088326448029060581129526446193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-661343238599416951818890258088436532500000000000)
      constant := (22223506999757453902986111493524282574128499146468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree123.table
  base := (4515382045226616753971112426203968411897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-235498656689609048682470908289392500000000000)
      constant := (7915545526552263683316555416843949547643727770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55123848904692811301/10000000000000000000)
  centralHi := (551238489046928113011/100000000000000000000)
  directionLo := (17296657893865732553/3125000000000000000)
  directionHi := (553493052603703441697/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree124.table
  base := (362111116065003124165575395743068821121/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-666716956292531248158534473138271372500000000000)
      constant := (22592635230188649156386231346766475564095128569472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree124.table
  base := (46350222856246536106674116363617237441933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2136709725911091706071274867840372500000000000)
      constant := (72423180711376665921636141270290220445503058277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17296657893865732553/3125000000000000000)
  centralHi := (553493052603703441697/100000000000000000000)
  directionLo := (111147693948977954547/20000000000000000000)
  directionHi := (8683413589763902699/1562500000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree125.table
  base := (19024450951108878345963835880063975648219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1344181347971291088996357376376212425000000000000)
      constant := (45929637829639471459943852981246240122140827945055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree125.table
  base := (95122254755419176447940934482900815629507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4307863083231403948000623122152425000000000000)
      constant := (147232492173139816622385834631545352104295103083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111147693948977954547/20000000000000000000)
  centralHi := (8683413589763902699/1562500000000000000)
  directionLo := (278987425446120019813/50000000000000000000)
  directionHi := (557974850892240039627/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree126.table
  base := (609831675208180178451637010330873493389/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-677464391678759840837822903237941052500000000000)
      constant := (23340058053649945017825128386954582088283189819280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree126.table
  base := (6098316752075168837248867919948504900263/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-241239261924479137992149806034672500000000000)
      constant := (8313233984949739067633163285750038305617806264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278987425446120019813/50000000000000000000)
  centralHi := (557974850892240039627/100000000000000000000)
  directionLo := (1400505760658545197/250000000000000000)
  directionHi := (560202304263418078801/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree127.table
  base := (12506610693230474707224452822153274341791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-682838109371874137177467118287775892500000000000)
      constant := (23718352646678637599135309749653565483863747290716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree127.table
  base := (50026442772876927108110664900943055031409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2188375173024922509858384947547892500000000000)
      constant := (76031760045307858908445467865801802963719994921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1400505760658545197/250000000000000000)
  centralHi := (560202304263418078801/100000000000000000000)
  directionLo := (112484187186620855349/20000000000000000000)
  directionHi := (281210467966552138373/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree128.table
  base := (102561707293074301363560914076217528684977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1376423654129976867034222666675221465000000000000)
      constant := (48199405387810564967941044101953955046941622081113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree128.table
  base := (102561707292998078262277651035143215376173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4411193977459065555574843281567465000000000000)
      constant := (154508417257697677860378137009454372538401592837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112484187186620855349/20000000000000000000)
  centralHi := (281210467966552138373/50000000000000000000)
  directionLo := (282315424945970108373/50000000000000000000)
  directionHi := (564630849891940216747/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree129.table
  base := (6568720829683637077109132340231930263549/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-693585544758102729856755548387445572500000000000)
      constant := (24484108195329439670313844779598051166793297038248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree129.table
  base := (26274883318718400327475785825001526922823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-246979867159349227301828703779952500000000000)
      constant := (8720716846129910044656480486265207894435901486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282315424945970108373/50000000000000000000)
  centralHi := (564630849891940216747/100000000000000000000)
  directionLo := (56683214810340500439/10000000000000000000)
  directionHi := (566832148103405004391/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree130.table
  base := (53833181745692053786599174601063970472291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-698959262451217026196399763437280412500000000000)
      constant := (24871569150950745484703194280076878050136150377179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree130.table
  base := (107666363491329375151674608693812389625183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4480081240277506627290990054510825000000000000)
      constant := (159456978008535510641083887895915824304904927527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56683214810340500439/10000000000000000000)
  centralHi := (566832148103405004391/100000000000000000000)
  directionLo := (71128116319838911237/12500000000000000000)
  directionHi := (569024930558711289897/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree131.table
  base := (110262197942369719428858986756502848584193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1408665960288662645072087956974230505000000000000)
      constant := (50524171121537800525788913941974981357746083608617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree131.table
  base := (22052439588464668835320923280556384825851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4514524871686727163149063440982505000000000000)
      constant := (161960641592287159351164965690290228115820170095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71128116319838911237/12500000000000000000)
  centralHi := (569024930558711289897/100000000000000000000)
  directionLo := (35700580958112788287/6250000000000000000)
  directionHi := (571209295329804612593/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree132.table
  base := (112887036627860282430051115957115743344561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1419413395674891237751376387073900185000000000000)
      constant := (51311314849567315995294343955901253532069608990809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree132.table
  base := (1763859947309702976479028555036702424369/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-252720472394219316611507601525232500000000000)
      constant := (9137994110088431160661492713618650541479812128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35700580958112788287/6250000000000000000)
  centralHi := (571209295329804612593/100000000000000000000)
  directionLo := (286692669310272775609/50000000000000000000)
  directionHi := (573385338620545551219/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree133.table
  base := (57770439773913700095182741579797723087807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-715080415530559915215332408586784932500000000000)
      constant := (26052284742994817640146067133582205414582298959383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree133.table
  base := (57770439773897055761779578636711673993381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2291706067252584117432605106962932500000000000)
      constant := (83513367588224017870177179519554864437405702589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286692669310272775609/50000000000000000000)
  centralHi := (573385338620545551219/100000000000000000000)
  directionLo := (143888288704037564231/25000000000000000000)
  directionHi := (23022126192646010277/4000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree134.table
  base := (11822372670224799404822796960249618961661/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-720454133223674211554976623636619772500000000000)
      constant := (26451967515402215791517050774038155248726121403545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree134.table
  base := (59111863351109896490213414919432759652877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2308927882957194385361641800198772500000000000)
      constant := (84794582588427472149203686492582239872691376613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143888288704037564231/25000000000000000000)
  centralHi := (23022126192646010277/4000000000000000000)
  directionLo := (577712836530961258967/100000000000000000000)
  directionHi := (72214104566370157371/12500000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree135.table
  base := (120935578091103435853422656657038110853913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1451655701833577015789241677372909225000000000000)
      constant := (53709411484011441125765031004363181415694642391297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree135.table
  base := (15116947261384943265765940637508206627047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-258461077629089405921186499270512500000000000)
      constant := (9565065776822869319470009504602152978427775708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577712836530961258967/100000000000000000000)
  centralHi := (72214104566370157371/12500000000000000000)
  directionLo := (289932237327308476111/50000000000000000000)
  directionHi := (579864474654616952223/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree136.table
  base := (61838216857189409746052715149116472173097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-731201568609902804234265053736289452500000000000)
      constant := (27260499422805226417696878370887959760404850773393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree136.table
  base := (61838216857179291537199097655028141473263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2343371514366414921219715186670452500000000000)
      constant := (87386395797158737592450442559450191750500469047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289932237327308476111/50000000000000000000)
  centralHi := (579864474654616952223/100000000000000000000)
  directionLo := (116401631679336977551/20000000000000000000)
  directionHi := (145502039599171221939/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree137.table
  base := (63223146786031174516900155457729761543809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-736575286303017100573909268786124292500000000000)
      constant := (27669348557800649839775613319293787446508786343721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree137.table
  base := (6322314678602260407539140063006368607543/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2360593330071025189148751879906292500000000000)
      constant := (88696994005685947990337559525244701873556183670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116401631679336977551/20000000000000000000)
  centralHi := (145502039599171221939/25000000000000000000)
  directionLo := (146035993832455220211/25000000000000000000)
  directionHi := (116828795065964176169/20000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree138.table
  base := (1615564470801810311339080073114596191117/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-741949003996131396913553483835959132500000000000)
      constant := (28081253146991925695375979845684028959506420750920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree138.table
  base := (129245157664130306794423005788984145035327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-528403365727918990461730794031585000000000000)
      constant := (20003863692663832957696810108770559075123083407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146035993832455220211/25000000000000000000)
  centralHi := (116828795065964176169/20000000000000000000)
  directionLo := (586272011431513013773/100000000000000000000)
  directionHi := (293136005715756506887/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree139.table
  base := (16509128248827401559121259037143956025429/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-747322721689245693253197698885793972500000000000)
      constant := (28496213190379004178658626353916250358750821750004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree139.table
  base := (132073025990606916444731008862800805451359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4790073922960491450013650532755945000000000000)
      constant := (182695147262124961216278093004502624742522706471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586272011431513013773/100000000000000000000)
  centralHi := (293136005715756506887/50000000000000000000)
  directionLo := (117678470224893366591/20000000000000000000)
  directionHi := (147098087781116708239/25000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree140.table
  base := (134929898551480279853939492799966448970771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1505392878764719979185683827871257625000000000000)
      constant := (57828457375923696494979050273538012393005993420299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree140.table
  base := (134929898551469866334063558490401287721641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4824517554369711985871723919227625000000000000)
      constant := (185375110095823055179138318427604516022643130529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117678470224893366591/20000000000000000000)
  centralHi := (147098087781116708239/25000000000000000000)
  directionLo := (147626269328921352967/25000000000000000000)
  directionHi := (590505077315685411869/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree141.table
  base := (8613485959170268373275133233860741261097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-758070157075474285932486128985463652500000000000)
      constant := (29335299639740431471363592782132888053373003163144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree141.table
  base := (137815775346715475191602681414029534304539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-539884576197659169081088589522145000000000000)
      constant := (20897184637229845721364025179945507882429181099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147626269328921352967/25000000000000000000)
  centralHi := (590505077315685411869/100000000000000000000)
  directionLo := (592610271434295463671/100000000000000000000)
  directionHi := (74076283929286932959/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree142.table
  base := (17591332047043595688676116886479972194691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (207866)
      previous := (103933)
      next := (103933)
      square := (1004945787408081819200300621120000000000000)
      linear := (-151446910289345086743132383264292500000000000)
      constant := (5903476700201296612912581340264883030079548076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree142.table
  base := (109945825294016638762252223956432730993/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (666)
      previous := (333)
      next := (333)
      square := (3219833423521800061517517120000000000000)
      linear := (-485360525410449618883938771292500000000000)
      constant := (18924201763525244912741881978344052530519680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592610271434295463671/100000000000000000000)
  centralHi := (74076283929286932959/12500000000000000000)
  directionLo := (594708013468168331921/100000000000000000000)
  directionHi := (297354006734084165961/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree143.table
  base := (71837270820176117488239299140375260785991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-768817592461702878611774559085133332500000000000)
      constant := (30186607905884752177173939986174440653179955392479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree143.table
  base := (143674541640345911344701442841134792721643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4927848448597373593445944078642665000000000000)
      constant := (193532531430201713806513952009468879410988221267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594708013468168331921/100000000000000000000)
  centralHi := (297354006734084165961/50000000000000000000)
  directionLo := (596798381999382456531/100000000000000000000)
  directionHi := (149199595499845614133/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree144.table
  base := (29329486227746818667241943463167203412873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1548382620309634349902837548269936345000000000000)
      constant := (61233690440500950027544359062287313192918292277685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree144.table
  base := (146647431138728738894989373780152568662033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-551365786667399347700446385012705000000000000)
      constant := (21810094387343241009018948567447909098625308353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596798381999382456531/100000000000000000000)
  centralHi := (149199595499845614133/25000000000000000000)
  directionLo := (598881454238571797633/100000000000000000000)
  directionHi := (299440727119285898817/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree145.table
  base := (29929864974298886330710052527644091420253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1559130055695862942582125978369606025000000000000)
      constant := (62100275977623810760469135580019169492748662513785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree145.table
  base := (149649324871489898074990899293988734810309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-4996735711415814665162090851586025000000000000)
      constant := (199068756347523890379084717021794099909608909021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598881454238571797633/100000000000000000000)
  centralHi := (299440727119285898817/50000000000000000000)
  directionLo := (300478653029101347757/50000000000000000000)
  directionHi := (120191461211640539103/20000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree146.table
  base := (152680222838633915138842526222569946575757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1569877491082091535261414408469275705000000000000)
      constant := (62972972423138095972613076927753065969708690422933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree146.table
  base := (152680222838630076760236818624338057026523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5031179342825035201020164238057705000000000000)
      constant := (201866252014505908908481448584554083309236321987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300478653029101347757/50000000000000000000)
  centralHi := (120191461211640539103/20000000000000000000)
  directionLo := (603026012024819743797/100000000000000000000)
  directionHi := (301513006012409871899/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree147.table
  base := (155740125040153677683008948360269742224587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1580624926468320127940702838568945385000000000000)
      constant := (63851779777043821720063272425907427103299087875203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree147.table
  base := (155740125040150428049313847530512022166299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-562846997137139526319804180503265000000000000)
      constant := (22742592943003919664921168055843926103740313259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603026012024819743797/100000000000000000000)
  centralHi := (301513006012409871899/50000000000000000000)
  directionLo := (75635955678787431189/12500000000000000000)
  directionHi := (605087645430299449513/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree148.table
  base := (31765806295211046721350906121229477172637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1591372361854548720619991268668615065000000000000)
      constant := (64736698039341009445856825095643873651480910478265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree148.table
  base := (79414515738026241269773121231689859756229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2550033302821738136368155505500532500000000000)
      constant := (103760004882556032024090956483418667247280353501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75635955678787431189/12500000000000000000)
  centralHi := (605087645430299449513/100000000000000000000)
  directionLo := (121428455664429748413/20000000000000000000)
  directionHi := (303571139161074371033/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree149.table
  base := (40486735536585100967046531301584899322459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-801059898620388656649639849384142372500000000000)
      constant := (32813863605014842467534134942412865581851759871142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree149.table
  base := (40486735536584518745271205106856315248819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2567255118526348404297192198736372500000000000)
      constant := (105188135924368176670467621196978260833047338422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell192.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121428455664429748413/20000000000000000000)
  centralHi := (303571139161074371033/50000000000000000000)
  directionLo := (304594990766441884033/50000000000000000000)
  directionHi := (609189981532883768067/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree150.table
  base := (165093857051011254412552004614952998588467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1612867232627005905978568128867954425000000000000)
      constant := (66524867289109877441831467078361194152694454170923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree150.table
  base := (165093857051009283005239904140429782124111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-574328207606879704939161975993825000000000000)
      constant := (23694680304212026569178379868370656531687643551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304594990766441884033/50000000000000000000)
  centralHi := (609189981532883768067/100000000000000000000)
  directionLo := (611230824708522865587/100000000000000000000)
  directionHi := (152807706177130716397/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree151.table
  base := (168269776190070044717139984180758154665463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1623614668013234498657856558967624105000000000000)
      constant := (67428118276581618960726663803229647759753594543247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree151.table
  base := (84134888095034187995196962808513416001667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2601698749935568940155265585208052500000000000)
      constant := (108073781216313912176310137394523702670579630123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611230824708522865587/100000000000000000000)
  centralHi := (152807706177130716397/25000000000000000000)
  directionLo := (306632438168113072541/50000000000000000000)
  directionHi := (613264876336226145083/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree152.table
  base := (171474699563519184894881299582039732531347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1634362103399463091337144989067293785000000000000)
      constant := (68337480172444943619360275442014432499858671317643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree152.table
  base := (42868674890879443109444926417662322312999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2618920565640179208084302278443892500000000000)
      constant := (109531295466447609377981121081287823802036903262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306632438168113072541/50000000000000000000)
  centralHi := (613264876336226145083/100000000000000000000)
  directionLo := (615292203771112710577/100000000000000000000)
  directionHi := (307646101885556355289/50000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree153.table
  base := (174708627171361199981258123477359416198203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1645109538785691684016433419166963465000000000000)
      constant := (69252952976699887172661460556047961115545391976307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree153.table
  base := (174708627171360004489137797245645017002569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-585809418076619883558519771484385000000000000)
      constant := (24666356470967837468152216453605861530709950329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615292203771112710577/100000000000000000000)
  centralHi := (307646101885556355289/50000000000000000000)
  directionLo := (617312873262285229773/100000000000000000000)
  directionHi := (308656436631142614887/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree154.table
  base := (177971559013598700248580842539860970831699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1655856974171920276695721849266633145000000000000)
      constant := (70174536689346486582527270241077297082855928397131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree154.table
  base := (177971559013597688436611101419493670053781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5306728394098799487884751329831145000000000000)
      constant := (224951414350073898423401623827662898316669990189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617312873262285229773/100000000000000000000)
  centralHi := (308656436631142614887/50000000000000000000)
  directionLo := (154831737494522575391/25000000000000000000)
  directionHi := (123865389995618060313/20000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree155.table
  base := (708060527696227955375814711518025548559/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-833302204779074434687505139683151412500000000000)
      constant := (35551115655192389834530404048799779351837132748288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree155.table
  base := (181263495090233500258788680764440676349231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5341172025508020023742824716302825000000000000)
      constant := (227925209266985423792529876578046284045288261239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154831737494522575391/25000000000000000000)
  centralHi := (123865389995618060313/20000000000000000000)
  directionLo := (310667249015320935321/50000000000000000000)
  directionHi := (621334498030641870643/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree156.table
  base := (7383377416050835202415996204932504155483/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1677351844944377462054298709465972505000000000000)
      constant := (72036036839814804821843271322526820007121038915675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree156.table
  base := (184584435401270155371114817657897645577031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-597290628546360062177877566974945000000000000)
      constant := (25657621443271692946270888664531522031353813271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310667249015320935321/50000000000000000000)
  centralHi := (621334498030641870643/100000000000000000000)
  directionLo := (311667790249816898957/50000000000000000000)
  directionHi := (124667116099926759583/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree157.table
  base := (187934379946711005177881442269076612018069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1688099280330606054733587139565642185000000000000)
      constant := (72975953277636600761527234895172094802310788093661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree157.table
  base := (46983594986677597977148187307350551387237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2705029644163230547729485744623092500000000000)
      constant := (116965782758726730410786474950602566831775110906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311667790249816898957/50000000000000000000)
  centralHi := (124667116099926759583/20000000000000000000)
  directionLo := (625330259455466609289/100000000000000000000)
  directionHi := (62533025945546660929/10000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree158.table
  base := (38262665745311495185368760128525697319251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1698846715716834647412875569665311865000000000000)
      constant := (73921980623850206343590813732233862087542205567095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree158.table
  base := (38262665745311391393550393077057026314863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5444502919735681631317044875717865000000000000)
      constant := (236964126851010221340957178766870911134395097235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625330259455466609289/100000000000000000000)
  centralHi := (62533025945546660929/10000000000000000000)
  directionLo := (627318595981712411053/100000000000000000000)
  directionHi := (313659297990856205527/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree159.table
  base := (48680320435203258615307117597032299060569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-304306541670178576022101103553752500000000000)
      constant := (13327539850205706727909797677156510420378656658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree159.table
  base := (194721281740812595326506456582700290694101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-608771839016100240797235362465505000000000000)
      constant := (26668475221123960289157762712314627165388963141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627318595981712411053/100000000000000000000)
  centralHi := (313659297990856205527/50000000000000000000)
  directionLo := (629300650196940974683/100000000000000000000)
  directionHi := (157325162549235243671/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree160.table
  base := (198158238989480411811634423964857711599337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1720341586489291832771452429864651225000000000000)
      constant := (75832368041453001594801349370516071007199872207953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree160.table
  base := (198158238989480040237577354611355432490997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5513390182554122703033191648661225000000000000)
      constant := (243088015934769848610903711861254584616684042893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629300650196940974683/100000000000000000000)
  centralHi := (157325162549235243671/25000000000000000000)
  directionLo := (315638240637964527529/50000000000000000000)
  directionHi := (631276481275929055059/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree161.table
  base := (201624200472562320351290942543848046142237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1731089021875520425450740859964320905000000000000)
      constant := (76796728112842268343466449490116608019631373958053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree161.table
  base := (40324840094512401191182921670972412667227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5547833813963343238891265035132905000000000000)
      constant := (246179343684972962509441545349040301951497108815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315638240637964527529/50000000000000000000)
  centralHi := (631276481275929055059/100000000000000000000)
  directionLo := (633246147470274111011/100000000000000000000)
  directionHi := (158311536867568527753/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree162.table
  base := (51279791547515361930069625893684992510501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-870918228630874509065014645031995292500000000000)
      constant := (38883599546311749350415147221677237356862356869338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree162.table
  base := (25639895773757647714373196257201460835493/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (373034)
      previous := (186517)
      next := (186517)
      square := (1803464476441488234456644866880000000000000)
      linear := (-310126524742920209708296578978032500000000000)
      constant := (13849458902262505905881474732120255256286880852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633246147470274111011/100000000000000000000)
  centralHi := (158311536867568527753/25000000000000000000)
  directionLo := (635209706128432743839/100000000000000000000)
  directionHi := (3970060663302704649/625000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree163.table
  base := (41728627228396090393437289090950059746133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1752583892647977610809317720163660265000000000000)
      constant := (78743780980796730305310119473532450325639201882385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree163.table
  base := (208643136141980226912548873033849701201427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5616721076781784310607411808076265000000000000)
      constant := (252420765602026400654395622783461462093807541563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635209706128432743839/100000000000000000000)
  centralHi := (3970060663302704649/625000000000000000)
  directionLo := (637167213715203355463/100000000000000000000)
  directionHi := (79645901714400419433/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree164.table
  base := (212196110328321957706064587013827148358593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1763331328034206203488606150263329945000000000000)
      constant := (79726473777362000321884429789701982441295749482217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree164.table
  base := (212196110328321767304982980868517744518067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5651164708191004846465485194547945000000000000)
      constant := (255570859768876964682969912679316121551040181723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637167213715203355463/100000000000000000000)
  centralHi := (79645901714400419433/12500000000000000000)
  directionLo := (31955936291533587571/5000000000000000000)
  directionHi := (639118725830671751421/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree165.table
  base := (215778088749088553119024857300844342682349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1774078763420434796167894580362999625000000000000)
      constant := (80715277482319345399649333084111133664763475156981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree165.table
  base := (215778088749088392041553212580010291627219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-631734259955580598035950953446625000000000000)
      constant := (28748949193475212873189159236030456880092810979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31955936291533587571/5000000000000000000)
  centralHi := (639118725830671751421/100000000000000000000)
  directionLo := (641064297228637672831/100000000000000000000)
  directionHi := (5008314822098731819/781250000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree166.table
  base := (219389071404282787662161011600562269323621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1784826198806663388847183010462669305000000000000)
      constant := (81710192095668801639333975011436754209270989051949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree166.table
  base := (219389071404282651397156625309627298306249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5720051971009445918181631967491305000000000000)
      constant := (261929814519226369885014988703779070896856210881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641064297228637672831/100000000000000000000)
  centralHi := (5008314822098731819/781250000000000000)
  directionLo := (643003981834539534057/100000000000000000000)
  directionHi := (321501990917269767029/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree167.table
  base := (44605811658781434071081186450413262895963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2095705012)
      previous := (1047852506)
      next := (1047852506)
      square := (10131863428648280901177430862131840000000000000)
      linear := (-1795573634192891981526471440562338985000000000000)
      constant := (82711217617410404569084629554257408448803827488735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree167.table
  base := (223029058293907055084902881374183845184577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6714612)
      previous := (3357306)
      next := (3357306)
      square := (32462360575946788220219607603840000000000000)
      linear := (-5754495602418666454039705353962985000000000000)
      constant := (265138675102725440625081651687482581872179073913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643003981834539534057/100000000000000000000)
  centralHi := (321501990917269767029/50000000000000000000)
  directionLo := (322468916381446983621/50000000000000000000)
  directionHi := (644937832762893967243/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree168.table
  base := (56674512354491042139057885293690503422069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-903160534789560287102879935331004332500000000000)
      constant := (41859177023772094563550041269853341573053150739322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree168.table
  base := (226698049417964071049062240940402968026491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (746068)
      previous := (373034)
      next := (373034)
      square := (3606928952882976468913289733760000000000000)
      linear := (-643215470425320776655308748937185000000000000)
      constant := (29818569387974915560785113278765411361821541131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell192.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322468916381446983621/50000000000000000000)
  centralHi := (644937832762893967243/100000000000000000000)
  directionLo := (646865902334266129761/100000000000000000000)
  directionHi := (323432951167133064881/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 31933
  qDenominator := 60208
  table := BinomialMassData.Q31933_60208.Degree169.table
  base := (11519802238822810356665003890702253322089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1047852506)
      previous := (523926253)
      next := (523926253)
      square := (5065931714324140450588715431065920000000000000)
      linear := (-908534252482674583442524150380839172500000000000)
      constant := (42365800693035094824965197041124923838934666730410) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31933_60208.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 113
  qDenominator := 213
  table := BinomialMassData.Q113_213.Degree169.table
  base := (115198022388228062327510070094968162259117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3357306)
      previous := (1678653)
      next := (1678653)
      square := (16231180287973394110109803801920000000000000)
      linear := (-2911691432618553762877926063453172500000000000)
      constant := (135807581343186439093685132011061393053533879173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q113_213.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell192.Kernel169
