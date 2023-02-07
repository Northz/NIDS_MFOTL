## Testing Verimon's algorithm

### Why do we have a separate directory to test files?
Verimon's theory files take too long to load in Isabelle. If we just want to test Verimon's behaviour, it is convenient to start a new Isabelle session with all Verimon's theory files already loaded.

### Ok, how do I do that?
You need the correct setup. 
1. First, you need isabelle commands enabled from the terminal. You can enable them by adding them to your PATH variable in a Command-Line session, with the command:
```
$ export PATH=$PATH:/path_to_where_your_Isabelle_app_is/working_Isabelle_version_application/bin
```

2. Then, allow Isabelle to find the Verimon repository. You do this by modifying the ROOTS file in your
```
~/.isabelle/working_Isabelle_version_application_directory/
``` 
by adding
```
/path_to_where_your_version_of_verimon_repo_is/monpoly/thys
```
as the last line of that file the path.

3. In your command line, typing
```
$ isabelle jedit -R Testing_Verified_Monitor
```
should launch Isabelle and load Verimon theories. This will take a while only the first time you do this.

### Why do we have `Monitor_Impl.thy` in the `Testing_Verified_Monitor` directory too?
Because I was not patient nor knowledgeable enough to test if `Monitor_Impl.thy` builds or if it starts some infinite-loop. So, the current solution is to simply update this directory's duplicated version whenever you do changes to `MFODL_Monitor_Devel/Monitro_Impl.thy`.