// --------------------------------------------------------------------------------------
// Implements type inference for JSON
// --------------------------------------------------------------------------------------

module ProviderImplementation.JsonInference

open System
open FSharp.Data
open FSharp.Data.Runtime
open FSharp.Data.Runtime.StructuralTypes

/// Infer type of a JSON value - this is simple function because most of the
/// functionality is handled in `StructureInference` (most notably, by
/// `inferCollectionType` and various functions to find common subtype), so
/// here we just need to infer types of primitive JSON values.


let rec inferLocalType inferTypesFromValues cultureInfo parentName json =
  let inline inRangeDecimal lo hi (v:decimal) : bool = (v >= decimal lo) && (v <= decimal hi)
  let inline inRangeFloat lo hi (v:float) : bool = (v >= float lo) && (v <= float hi)
  let inline isIntegerDecimal (v:decimal) : bool = Math.Round v = v
  let inline isIntegerFloat (v:float) : bool = Math.Round v = v

  match json with
  // Null and primitives without subtyping hiearchies
  | JsonValue.Null -> InferedType.Null
  | JsonValue.Boolean _ -> InferedType.Primitive(typeof<bool>, None, false)
  | JsonValue.String s when inferTypesFromValues -> StructuralInference.getInferedTypeFromString cultureInfo s None
  | JsonValue.String _ -> InferedType.Primitive(typeof<string>, None, false)
  // For numbers, we test if it is integer and if it fits in smaller range
  | JsonValue.Number 0M when inferTypesFromValues -> InferedType.Primitive(typeof<Bit0>, None, false)
  | JsonValue.Number 1M when inferTypesFromValues -> InferedType.Primitive(typeof<Bit1>, None, false)
  | JsonValue.Number n when inferTypesFromValues && inRangeDecimal Int32.MinValue Int32.MaxValue n && isIntegerDecimal n -> InferedType.Primitive(typeof<int>, None, false)
  | JsonValue.Number n when inferTypesFromValues && inRangeDecimal Int64.MinValue Int64.MaxValue n && isIntegerDecimal n -> InferedType.Primitive(typeof<int64>, None, false)
  | JsonValue.Number _ -> InferedType.Primitive(typeof<decimal>, None, false)
  | JsonValue.Float f when inferTypesFromValues && inRangeFloat Int32.MinValue Int32.MaxValue f && isIntegerFloat f -> InferedType.Primitive(typeof<int>, None, false)
  | JsonValue.Float f when inferTypesFromValues && inRangeFloat Int64.MinValue Int64.MaxValue f && isIntegerFloat f -> InferedType.Primitive(typeof<int64>, None, false)
  | JsonValue.Float _ -> InferedType.Primitive(typeof<float>, None, false)
  // More interesting types 
  | JsonValue.Array ar -> StructuralInference.inferCollectionType (*allowEmptyValues*)false (Seq.map (inferLocalType inferTypesFromValues cultureInfo (NameUtils.singularize parentName)) ar)
  | JsonValue.Record properties ->
      let name = 
        if String.IsNullOrEmpty parentName 
        then None 
        else Some parentName
      let props = 
        [ for propName, value in properties -> 
            let t = inferLocalType inferTypesFromValues cultureInfo propName value
            { Name = propName
              Type = t } ]
      InferedType.Record(name, props, false)

let isComplex = function
    | InferedType.Record _ 
    | InferedType.Collection _ -> true
    | _ -> false

let rec types x =
    seq {
        match x with
        | InferedType.Record(Some name, fields, false) ->
            yield name, InferedType.Record(Some name, fields, false)
            yield! fields |> Seq.map (fun p -> p.Name, p.Type)
            yield! fields |> Seq.collect (fun x -> types x.Type)
        | InferedType.Collection (_, m) ->
            yield! m |> Map.toSeq |> Seq.collect (snd >> snd >> types)
        | _ -> ()
    }

let rec properties t =
    seq {
        match t with
        | InferedType.Record (_name, fields, _optional) ->
            yield! fields
            yield! fields |> Seq.collect (fun x -> properties x.Type)
        | InferedType.Collection (_, m) ->
            yield! m |> Map.toSeq |> Seq.collect (snd >> snd >> properties)
        | _ -> ()
    }        

let patchType groupedTypes=
    properties
    //>> Seq.filter isComplex
    >> Seq.toList
    >> List.iter(fun p ->
        groupedTypes |> Map.tryFind p.Name
        |> Option.iter (fun t ->
            p.Type <- t
            ) )

// normalize properties of the inferedType which don't affect code generation
let rec normalize  = function
    | InferedType.Heterogeneous map -> 
        map 
        |> Map.map (fun _ inferedType -> normalize inferedType) 
        |> InferedType.Heterogeneous
    | InferedType.Collection (order, types) -> 
        InferedType.Collection (order, Map.map (fun _ (multiplicity, inferedType) -> multiplicity, normalize inferedType) types)
    | InferedType.Record (name, props, optional) -> 
        let props = props |> List.map (fun { Name = name; Type = inferedType } -> { Name = name; Type = normalize inferedType })
        InferedType.Record (name, props, optional)
    | InferedType.Primitive (typ, unit, optional) when typ = typeof<Bit0> || typ = typeof<Bit1> -> InferedType.Primitive (typeof<int>, unit, optional)
    | InferedType.Primitive (typ, unit, optional) when typ = typeof<Bit> -> InferedType.Primitive (typeof<bool>, unit, optional)
    | x -> x

let inferTypes inferTypesFromValues cultureInfo parentName globalInference =
    if globalInference then
        fun x ->
            let samples = x |> Array.map (inferLocalType inferTypesFromValues cultureInfo parentName >> normalize)
            let initialType = samples |> Array.reduce (StructuralInference.subtypeInfered false)

            let types = samples |> Seq.collect types

            let nonEmptyCollection = function
                | InferedType.Collection (_, EmptyMap () _) -> false
                | _ -> true

            let groupedTypes =
                types
                |> Seq.filter (snd >> nonEmptyCollection)
                |> Seq.groupBy fst
                |> Seq.map (fun (name, possibleTypes) -> name, possibleTypes |> Seq.map snd |> Seq.fold (StructuralInference.subtypeInfered false) InferedType.Top )
                |> Map.ofSeq

            patchType groupedTypes initialType
            initialType
    else
        Array.map (inferLocalType inferTypesFromValues cultureInfo parentName)
        >> Array.fold (StructuralInference.subtypeInfered false) InferedType.Top



let inferType inferTypesFromValues cultureInfo parentName _globalInference json =
    inferLocalType inferTypesFromValues cultureInfo parentName json

