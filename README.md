## Requirements
* Isabelle2019 (or newer)
   * Download [here](https://isabelle.in.tum.de/)

## Open Theorie
Isabelle requires further configuration to work with the session-dokument. There are 2 possible ways:
1. commend-line argument. Start isabelle with `isabelle jedit -d <pathToProjectRoot>`. To reduce the startup time you should also use the `-l <sessionName>` flag with a sessionName listed below.
   * Example: `isabelle jedit -d . -l spec automat/ndAutomaton.thy`
2. ROOTS file. If you are in **only** one montibelle-project you can add the project root to you isabelle ROOTS file and start isabelle normally. The ROOTS file location varies based on your operating system. 
   *  Example: For ArchLinux it is in `/opt/isabelle`. There you can add `<PathToMontibelleProject>` as last element.
   *  **Windows**: Since Isabelle is running using Cygwin, adding windows path at the end of ROOTS file wont work. To get unix path of the folder, start **Cygwin-Terminal.bat** 
        (located in Isabelle root folder), the Cygwin console will open and you are at user's home folder. The command **pwd** shows the path of the current location.
        You then navigate to the project folder using **cd** command. The command **pwd** will show the `<PathToMontibelleProject>`.
   
## Sessions
You can use prebuild sessions to reduce the startup time. If you start with this option you cannot change documents in the session!
1. inc
2. stream
3. bundle
4. spf
5. automaton