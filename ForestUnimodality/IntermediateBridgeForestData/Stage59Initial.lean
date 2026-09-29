import ForestUnimodality.IntermediateBridgeForest
import ForestUnimodality.IntermediateBridgeCoverData.Rectangles
import ForestUnimodality.Stage59InitialRectangles

namespace ForestUnimodality.IntermediateBridgeForestData
open IntermediateBridgeCover IntermediateBridgeCoverData
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem stage59_cell000 : (rectangle (59,0)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨0,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨0,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨0,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨0,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨0,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell000

theorem stage59_cell001 : (rectangle (59,1)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨1,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨1,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨1,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨1,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨1,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell001

theorem stage59_cell002 : (rectangle (59,2)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨2,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨2,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨2,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨2,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨2,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell002

theorem stage59_cell003 : (rectangle (59,3)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨3,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨3,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨3,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨3,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨3,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell003

theorem stage59_cell004 : (rectangle (59,4)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨4,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨4,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨4,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨4,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨4,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell004

theorem stage59_cell005 : (rectangle (59,5)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨5,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨5,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨5,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨5,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨5,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell005

theorem stage59_cell006 : (rectangle (59,6)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨6,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨6,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨6,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨6,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨6,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell006

theorem stage59_cell007 : (rectangle (59,7)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨7,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨7,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨7,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨7,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨7,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell007

theorem stage59_cell008 : (rectangle (59,8)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨8,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨8,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨8,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨8,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨8,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell008

theorem stage59_cell009 : (rectangle (59,9)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨9,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨9,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨9,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨9,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨9,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell009

theorem stage59_cell010 : (rectangle (59,10)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨10,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨10,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨10,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨10,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨10,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell010

theorem stage59_cell011 : (rectangle (59,11)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨11,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨11,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨11,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨11,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨11,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell011

theorem stage59_cell012 : (rectangle (59,12)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨12,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨12,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨12,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨12,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨12,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell012

theorem stage59_cell013 : (rectangle (59,13)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨13,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨13,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨13,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨13,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨13,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell013

theorem stage59_cell014 : (rectangle (59,14)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨14,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨14,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨14,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨14,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨14,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell014

theorem stage59_cell015 : (rectangle (59,15)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨15,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨15,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨15,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨15,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨15,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell015

theorem stage59_cell016 : (rectangle (59,16)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨16,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨16,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨16,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨16,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨16,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell016

theorem stage59_cell017 : (rectangle (59,17)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨17,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨17,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨17,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨17,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨17,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell017

theorem stage59_cell018 : (rectangle (59,18)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨18,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨18,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨18,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨18,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨18,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell018

theorem stage59_cell019 : (rectangle (59,19)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨19,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨19,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨19,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨19,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨19,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell019

theorem stage59_cell020 : (rectangle (59,20)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨20,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨20,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨20,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨20,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨20,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell020

theorem stage59_cell021 : (rectangle (59,21)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨21,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨21,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨21,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨21,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨21,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell021

theorem stage59_cell022 : (rectangle (59,22)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨22,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨22,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨22,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨22,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨22,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell022

theorem stage59_cell023 : (rectangle (59,23)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨23,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨23,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨23,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨23,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨23,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell023

theorem stage59_cell024 : (rectangle (59,24)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨24,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨24,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨24,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨24,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨24,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell024

theorem stage59_cell025 : (rectangle (59,25)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨25,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨25,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨25,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨25,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨25,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell025

theorem stage59_cell026 : (rectangle (59,26)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨26,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨26,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨26,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨26,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨26,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell026

theorem stage59_cell027 : (rectangle (59,27)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨27,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨27,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨27,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨27,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨27,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell027

theorem stage59_cell028 : (rectangle (59,28)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨28,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨28,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨28,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨28,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨28,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell028

theorem stage59_cell029 : (rectangle (59,29)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨29,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨29,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨29,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨29,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨29,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell029

theorem stage59_cell030 : (rectangle (59,30)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨30,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨30,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨30,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨30,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨30,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell030

theorem stage59_cell031 : (rectangle (59,31)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨31,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨31,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨31,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨31,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨31,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell031

theorem stage59_cell032 : (rectangle (59,32)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨32,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨32,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨32,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨32,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨32,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell032

theorem stage59_cell033 : (rectangle (59,33)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨33,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨33,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨33,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨33,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨33,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell033

theorem stage59_cell034 : (rectangle (59,34)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨34,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨34,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨34,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨34,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨34,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell034

theorem stage59_cell035 : (rectangle (59,35)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨35,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨35,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨35,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨35,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨35,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell035

theorem stage59_cell036 : (rectangle (59,36)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨36,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨36,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨36,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨36,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨36,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell036

theorem stage59_cell037 : (rectangle (59,37)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨37,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨37,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨37,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨37,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨37,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell037

theorem stage59_cell038 : (rectangle (59,38)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨38,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨38,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨38,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨38,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨38,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell038

theorem stage59_cell039 : (rectangle (59,39)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨39,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨39,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨39,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨39,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨39,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell039

theorem stage59_cell040 : (rectangle (59,40)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨40,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨40,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨40,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨40,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨40,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell040

theorem stage59_cell041 : (rectangle (59,41)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨41,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨41,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨41,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨41,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨41,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell041

theorem stage59_cell042 : (rectangle (59,42)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨42,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨42,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨42,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨42,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨42,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell042

theorem stage59_cell043 : (rectangle (59,43)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨43,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨43,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨43,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨43,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨43,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell043

theorem stage59_cell044 : (rectangle (59,44)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨44,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨44,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨44,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨44,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨44,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell044

theorem stage59_cell045 : (rectangle (59,45)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨45,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨45,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨45,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨45,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨45,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell045

theorem stage59_cell046 : (rectangle (59,46)).ForestValid := by
  intro V _ G S B z k hB hG hz hk hpoint hrank hmean hhalf
  have hp : 59≤S.card ∧ S.card≤79 ∧
      z/(1+z)∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨46,by decide⟩).qa:ℝ) ((Stage59InitialRectangles.rectangle ⟨46,by decide⟩).qb:ℝ) ∧
      hardCoreAvailableMean G S B z∈Set.Icc ((Stage59InitialRectangles.rectangle ⟨46,by decide⟩).mlo:ℝ) ((Stage59InitialRectangles.rectangle ⟨46,by decide⟩).mhi:ℝ) := hpoint
  rcases hp with ⟨hn,hN,hq,hm⟩
  exact Stage59InitialRectangles.no_weak_valley ⟨46,by decide⟩ k hB hG hn hN hz hq hrank hmean hm
#print axioms stage59_cell046

end ForestUnimodality.IntermediateBridgeForestData
