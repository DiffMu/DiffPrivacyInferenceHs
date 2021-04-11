# DiffPrivacyInferenceHs

## Developer Guide
### Folder structure
The subfolders are organized as follows:
```
- app  (main entry point into application)
- src  (actual source code)
  \- DiffMu
     |- Prelude    (Common imports from libraries)
     |- Abstract   (Structures/Code useful for building typecheckers,
     |              should not contain references to the actual duet type system)
     |- Core       (Basic definitions of the duet type system, operations on contexts, etc.)
     |- Typecheck  (Implementation of the actual typechecking and subtyping rules)
```



