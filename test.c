    #include <stdio.h>
    #include <stdlib.h>
    #include <string.h>

    int array[100];
    char* string[100];
    

    int getint() {
      char str[100];
      int n = scanf("%s", str);
      if(n != 1){
        printf("Unexpected end of input!\n");
        exit(1);
      }else{
        for(int k = 0; str[k]!='\0' ; k++){
          if(str[k] >'9' || str[k] <'0'){
            printf("non numeric input!\n");
            exit(1);
          }
        }
        return atoi(str);
      }
    }

    void putint(int n) {
      printf("%d\n", n);
    }

    int divisionE(){
      printf("A division by zero erro here!\n");
      exit(1);
      return 1;
    }
    
    int divide (int a, int b){
      if(b == 0){
        divisionE();
      }
      return a/b ;
    }
    

    int getvar(char* a){
      for(int i = 0; string [i] != 0;i++){
        if(!strcmp(string[i],a)){
          return array[i];
        }
      }
      printf("Use of uninitialized variable %s\n", a);
      exit (1);
    }

    int setvar(char* a, int n){
      int i;
      for(i = 0; string [i] != 0;i++){
        if(!strcmp(string[i],a)){
          array[i] = n;
          return 1;
        }
      }
      string[i] = a;
      array[i] = n; 
      return 0;
    }
    
    
    
    int main(int argc, char* argv[]) {


    setvar("a", getint()); 
setvar("b", getint()); 
putint(divide (getvar( "a"), getvar( "b")) );
}