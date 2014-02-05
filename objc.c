/*
*   $Id$
*
*   Copyright (c) 2007 Andrew Ruder <andy@aeruder.net>
*
*   This source code is released for free distribution under the terms of the
*   GNU General Public License.
*
*   This module contains functions for generating tags for Objective-C language
*   files.
*/

/*
*   INCLUDE FILES
*/
#include "general.h"  /* must always come first */

#include <string.h>
#include <stdio.h>

#include "get.h"
#include "entry.h"
#include "parse.h"
#include "read.h"
#include "vstring.h"
#include "routines.h"

/*
*   DATA DECLARATIONS
*/
typedef enum {
	K_UNDEFINED = -1,
	K_PROTOCOL, K_INTERFACE, K_IMPLEMENTATION, K_INTMETHOD,
	K_IMPMETHOD, K_PMETHOD
} objcKind;

/*
*   DATA DEFINITIONS
*/
static kindOption ObjCKinds [] = {
	{ TRUE, 'P', "protocol", "protocols" },
	{ TRUE, 'i', "interface", "class interfaces" },
	{ TRUE, 'I', "implementation", "class implementations" },
	{ TRUE, 'M', "intmethod", "instance methods" },
	{ TRUE, 'C', "impmethod", "implementation methods" },
	{ TRUE, 'Z', "pmethod", "protocol methods" }
};

static vString *ReturnType;
static vString *Signature;

struct handlerType {
	const char *name;
	void (*handler)(const char *keyword);
};

static void protocolHandler(const char *keyword);
static void interfaceHandler(const char *keyword);
static void implementationHandler(const char *keyword);

/**
 * Function mappings for the various
 * Obj-C keywords we handle
 */
static struct handlerType handlers[] = {
	{ "protocol", protocolHandler },
	{ "interface", interfaceHandler },
	{ "implementation", implementationHandler },
	{ NULL, 0 }
};

/**
 * This does a LOT of our parsing, you pass it a function
 * that returns false when it should stop and this takes
 * care of the vString stuff and checking for EOF etc..
 */
static char *readToFalse(int (*shouldcontinue)(int c, int pos), int *ender)
{
	static vString *wordBuffer = 0;
	int len = 0;
	int z;

	if (!wordBuffer) {
		wordBuffer = vStringNew();
	} else {
		vStringClear(wordBuffer);
	}

	while ((z = cppGetc()) != EOF && shouldcontinue(z, len)) {
		vStringPut(wordBuffer, z);
		len++;
	}
	cppUngetc(z);

	if (ender) *ender = z;

	vStringPut(wordBuffer, 0);
	return vStringValue(wordBuffer);
}

/**
 * Read to non-alpha
 */
static int myIsAlpha(int c, int pos)
{
	return isalpha(c);
}
static char *readToNonAlpha(int *ender)
{
	return readToFalse(myIsAlpha, ender);
}

/**
 * Read to a non-space
 */
static int myIsSpace(int c, int pos)
{
	return isspace(c);
}
static char *readToNonSpace(int *ender)
{
	return readToFalse(myIsSpace, ender);
}

/**
 * Read a C identifier
 */
static int myIsIdentifier(int c, int pos)
{
	if (pos == 0)
		return isalpha(c) || c == '_';
	return isalpha(c) || isdigit(c) || c == '_';
}
static char *readToNonIdentifier(int *ender)
{
	return readToFalse(myIsIdentifier, ender);
}

/**
 * This will look for the beginning of a method declaration *OR*
 * some braces/obj-c keyword/etc..
 */
static int myIsNotMethod(int c, int pos)
{
	return c != '-' && c != '+' && c != '@' && c != '{' && c != '[';
}
static char *readToMethod(int *ender)
{
	return readToFalse(myIsNotMethod, ender);
}

/**
 * This will parse braces/quotes/parens to get us out
 * of the current 'chunk'.  It isn't very smart, something
 * like this will register just fine:
 *   ({)}
 * but hey, I don't think that's valid obj-c in any way, so
 * I'm not going to worry about it.
 */
static int myIsNotMatchingBrace(int c, int pos)
{
	static int braces;
	static int parens;
	static int skipnext;
	static int inQuotes;
	static int squares;

	if (pos == 0) {
		braces = 0;
		parens = 0;
		inQuotes = 0;
		skipnext = 0;
		squares = 0;
	}

	if (skipnext) {
		skipnext = 0;
		return 1;
	}

	/* Ignore any braces in quotes */
	if (inQuotes && c != '"' && c != '\'') {
		return 1;
	}

	switch (c) {
		case '\'':
		case '"':
			if (inQuotes && inQuotes != c) return 1;
			if (inQuotes && inQuotes == c) {
				inQuotes = 0;
				break;
			}
			if (!inQuotes) inQuotes = c;
			break;
		case '{':
			braces++;
			break;
		case '\\':
			skipnext = 1;
			break;
		case '}':
			braces--;
			break;
		case '(':
			parens++;
			break;
		case ')':
			parens--;
			break;
		case '[':
			squares++;
			break;
		case ']':
			squares--;
			break;
		default:
			break;
	}


	return parens || braces || inQuotes || squares;
}

static char *readToMatchingBrace(int *ender)
{
	return readToFalse(myIsNotMatchingBrace, ender);
}

/**
 * An easier to use alternative to readToNonSpace
 */
int skipToNonWhite(void)
{
	int z;
	readToNonSpace(&z);
	return z;
}

/**
 * An easier to use front-end to readToMethod
 */
int skipToMethod(void)
{
	int z;
	readToMethod(&z);
	return z;
}

/**
 * Find a @ that isn't in a string
 */
static int skipToObjCKeyword (void)
{
	int z;
	while ((z = skipToNonWhite()) != EOF)
	{
		cppGetc();
		if (z == '"') readToMatchingBrace(0);
		if (z == '@') break;
	}

	return z;
}

/**
 * Reads from 'start' to 'end' and eliminates all spaces
 * inbetween.
 */
static char *readBetweenDelimitersWhileTrimmingSpaces(char start, char end)
{
	static vString *wordBuffer = 0;
	int z;
	if (!wordBuffer)
		wordBuffer = vStringNew();
	else
		vStringClear(wordBuffer);

	z = skipToNonWhite();
	if (z != start) return NULL;
	while ((z = cppGetc()) != EOF && z != end) {
		if (isspace(z)) continue;
		vStringPut(wordBuffer, z);
	}
	if (z == EOF) return NULL;
	vStringPut(wordBuffer, z);
	vStringPut(wordBuffer, 0);
	return vStringValue(wordBuffer);
}

/**
 * Read a protocol tag like <Blah>.
 * It also folds down the spaces.
 * Returns NULL if it fails.
 */
static char *readProtocolTag(void)
{
	return readBetweenDelimitersWhileTrimmingSpaces('<', '>');
}

/**
 * Read a category tag like (Blah).
 * It also folds down the spaces.
 * Returns NULL if it fails.
 */
static char *readCategoryTag(void)
{
	return readBetweenDelimitersWhileTrimmingSpaces('(', ')');
}



/**
 * Record the current position in the file.  This is used
 * when emitting the Obj-C tag and we can get the first
 * line of whatever we are emitting.
 */
static unsigned recordedLineno = 0;
static fpos_t recordedPos;
static void recordPosition(void)
{
	recordedLineno = getSourceLineNumber();
	recordedPos = getInputFilePosition();
}

/**
 * Emit a tag with a given name, type, scope, and inheritance
 */
static void emitObjCTag(const char *name, objcKind type, const char *scope, const char *inheritance)
{
	tagEntryInfo tag;

	initTagEntry (&tag, name);
	tag.lineNumber = recordedLineno;
	tag.filePosition = recordedPos;

	if (scope && *scope) {
		switch(type) {
			case K_PMETHOD:
				tag.extensionFields.scope[0] = "protocol";
        if (vStringLength(ReturnType) > 0) {
          tag.extensionFields.returnType = eStrdup(vStringValue(ReturnType));
          vStringClear(ReturnType);
        }
        if (vStringLength(Signature) > 0) {
          tag.extensionFields.signature = eStrdup(vStringValue(Signature));
          vStringClear(Signature);
        }
				break;
			case K_INTMETHOD:
				tag.extensionFields.scope[0] = "interface";
        if (vStringLength(ReturnType) > 0) {
          tag.extensionFields.returnType = eStrdup(vStringValue(ReturnType));
          vStringClear(ReturnType);
        }
        if (vStringLength(Signature) > 0) {
          tag.extensionFields.signature = eStrdup(vStringValue(Signature));
          vStringClear(Signature);
        }
				break;
			case K_IMPMETHOD:
				tag.extensionFields.scope[0] = "implementation";
        if (vStringLength(ReturnType) > 0) {
          tag.extensionFields.returnType = eStrdup(vStringValue(ReturnType));
          vStringClear(ReturnType);
        }
        if (vStringLength(Signature) > 0) {
          tag.extensionFields.signature = eStrdup(vStringValue(Signature));
          vStringClear(Signature);
        }
				break;
			default:
				tag.extensionFields.scope[0] = "unknown";
		}
		tag.extensionFields.scope[1] = scope;
	}
	if (inheritance && *inheritance)
		tag.extensionFields.inheritance = inheritance;
	tag.kindName = ObjCKinds[type].name;
	tag.kind = ObjCKinds[type].letter;
	makeTagEntry(&tag);
}

/**
 * Parse a method starting with the -/+.  Return it in the method vString
 */
static void getSingleObjCMethod(vString *method)
{
	int z;
	int skipNextIdent;
	const char *temp;
  const char *returnTypeOrArg = NULL;
  boolean returnTypeDone = FALSE;
  boolean methodDone = FALSE;
  boolean inSignature = FALSE;

	vStringClear(method);
  vStringClear(ReturnType);
  vStringClear(Signature);

	recordPosition();
	z = cppGetc();
	vStringPut(method, z);
	skipNextIdent = 0;
  vStringPut(Signature, '(');
	while ((z = cppGetc()) != EOF && z != ';' && z != '{') {
		if (isspace(z))
			continue;
		else if (z == '(') {
			cppUngetc(z);
      returnTypeOrArg = readToMatchingBrace(&z);
      /* skip over an opening curly brace */
      if (*returnTypeOrArg == '(') {
        returnTypeOrArg++;
      }
      if (returnTypeDone == FALSE) {
        vStringCatS(ReturnType, returnTypeOrArg);
        /* fprintf(stderr, "DEBUG: ReturnType=%s\n", vStringValue(ReturnType)); */
        vStringTerminate(ReturnType);
        returnTypeDone = TRUE;
      }
      else {
        vStringCatS(Signature, returnTypeOrArg);
        inSignature = TRUE;
      }
    }
		else if (z == ':') {
			vStringPut(method, z);
      if (inSignature) {
        vStringPut(Signature, z);
      }
			skipNextIdent = 1;
		}
		else if (myIsIdentifier(z, 0)) {
			cppUngetc(z);
			temp = readToNonIdentifier(0);
      if (inSignature) {
        vStringPut(Signature, ' ');
        vStringCatS(Signature, temp);
        vStringCatS(Signature, ", ");
        inSignature = FALSE;
      }
      else if (methodDone) {
        vStringCatS(Signature, temp);
        inSignature = TRUE;
      }
			if (skipNextIdent)
				skipNextIdent = 0;
			else {
				vStringCatS(method, temp);
        methodDone = TRUE;
      }
		}
	}
  if (vStringLast(Signature) == ' ') {
    /* remove trailing ', ' and ' ' */
    vStringChop(Signature);
    vStringChop(Signature);
  }
  vStringPut(Signature, ')');
  vStringTerminate(Signature);
	cppUngetc(z);
	vStringPut(method, 0);
}

/**
 * Generate tags for all Obj-C methods until an @end.  scope and inheritance are
 * the class/protocol the method belongs to and the inheritance chain for that class
 */
static void readObjCMethods(objcKind mType, const char *scope, const char *inheritance)
{
	int z;
	const char *temp;
	vString *method = vStringNew();
  int c;

	while (1) {
		z = skipToNonWhite();
		if (z == EOF) break;
		z = skipToMethod();
		switch(z) {
			case '@':
				cppGetc();
				temp = readToNonAlpha(0);
				if (temp && !strcmp(temp, "end"))
					return;
				break;
			case '[':
			case '{':
				readToMatchingBrace(0);
				break;
			case '-':
			case '+':
				getSingleObjCMethod(method);
				emitObjCTag(vStringValue(method), mType, scope, inheritance);
				break;
			default:
				break;
		}
	}

	vStringDelete(method);
}


/**
 * We need to handle two forms here:
 *   @protocol ProtocolName; // Do Nothing
 *   @protocol ProtocolName | <OtherProtocols> |
 *   ...
 *   @end // Handle this protocol
 */
static void protocolHandler(const char *keyword)
{
	char *ident;
	char *proto = NULL;
	int z;
	z = skipToNonWhite();

	ident = readToNonIdentifier(0);
	if (ident && *ident)
		ident = eStrdup(ident);
	else
		return;

	z = skipToNonWhite();
	if (z == ';') {
		eFree(ident);
		return;
	}
	proto = readProtocolTag();
	if (proto && *proto)
		proto = eStrdup(proto);
	else
		proto = eStrdup("<>");

	emitObjCTag(ident, K_PROTOCOL, 0, proto);

	readObjCMethods(K_PMETHOD, ident, proto);

	eFree(ident);
	eFree(proto);
}

/**
 * interfaces in Obj-C look like:
 *
 * @interface Class1 [ : SuperClass | (CategoryName) ] [ <Protocols> ]
 * 	[ {
 * 	   ...
 * 	  }
 * 	]
 * 	methods
 * 	@end
 */
static void interfaceHandler(const char *keyword)
{
	char *ident;
	char *proto = NULL;
	char *superclass = NULL;
	char *inheritance;
	int z;

	z = skipToNonWhite();

	ident = readToNonIdentifier(0);
	if (ident && *ident)
		ident = eStrdup(ident);
	else
		return;
	z = skipToNonWhite();
	if (z == '(') {
		char *category;
		char *newIdent;
		category = readCategoryTag();
		if (category) {
			newIdent = eMalloc(strlen(category) + strlen(ident) + 1);
			strcpy(newIdent, ident);
			strcat(newIdent, category);
			eFree(ident);
			ident = newIdent;
		}
	} else if (z == ':') {
		cppGetc();
		skipToNonWhite();
		superclass = readToNonIdentifier(0);
	}
	if (superclass && *superclass)
		superclass = eStrdup(superclass);
	else
		superclass = eStrdup("");

	proto = readProtocolTag();
	if (proto && *proto)
		proto = eStrdup(proto);
	else
		proto = eStrdup("<>");

	inheritance = eMalloc(strlen(proto) + strlen(superclass) + 1);
	strcpy(inheritance, superclass);
	strcat(inheritance, proto);

	emitObjCTag(ident, K_INTERFACE, 0, inheritance);
	readObjCMethods(K_INTMETHOD, ident, inheritance);

	eFree(ident);
	eFree(proto);
	eFree(superclass);
	eFree(inheritance);
}

/**
 * implementations in Obj-C look like:
 *
 * @implementation Class1 [ (CategoryName) ]
 * 	[ {
 * 	   ...
 * 	  }
 * 	]
 * 	methods
 * 	@end
 */
static void implementationHandler(const char *keyword)
{
	char *ident;
	int z;

	z = skipToNonWhite();

	ident = readToNonIdentifier(0);
	if (ident && *ident)
		ident = eStrdup(ident);
	else
		return;
	z = skipToNonWhite();
	if (z == '(') {
		char *category;
		char *newIdent;
		category = readCategoryTag();
		if (category) {
			newIdent = eMalloc(strlen(category) + strlen(ident) + 1);
			strcpy(newIdent, ident);
			strcat(newIdent, category);
			eFree(ident);
			ident = newIdent;
		}
	}

	emitObjCTag(ident, K_IMPLEMENTATION, 0, 0);
	readObjCMethods(K_IMPMETHOD, ident, 0);

	eFree(ident);
}

/**
 * This is a very simple parser.  On the first pass it
 * basically looks for @keyword.
 * On the later passes, it hands it off to the C/C++ parser
 */
static rescanReason findObjCOrObjCppTags (const unsigned int passCount,
        parserDefinition *baseParser)
{
  int z;
	if (passCount == 1) {
		cppInit(0, 0);
    ReturnType = vStringNew();
    Signature = vStringNew();
		while ((z = skipToObjCKeyword()) != EOF) {
			struct handlerType *iter;
			char *keyword;

			recordPosition();
			keyword = readToNonAlpha(NULL);
			if (!keyword) continue;
			keyword = eStrdup(keyword);

			for (iter = handlers; iter->name; iter++)
				if (!strcmp(iter->name, keyword))
					iter->handler(keyword);

			eFree(keyword);
		}
    vStringDelete(Signature);
    vStringDelete(ReturnType);

		cppTerminate ();
	} else {
		if (baseParser && baseParser->parser2) {
			return baseParser->parser2(passCount - 1);
		}
	}

	return RESCAN_APPEND;
}

/*
 * Grab the C parser and hand it up to findObjCOrObjCppTags
 */
static rescanReason findObjCTags (const unsigned int passCount)
{
	static parserDefinition *cParser = 0;
	if (!cParser) {
		cParser = CParser();
	}
	return findObjCOrObjCppTags(passCount, cParser);
}

/**
 * Grab the C++ parser and hand it up to findObjCOrObjCppTags
 */
static rescanReason findObjCppTags (const unsigned int passCount)
{
	static parserDefinition *cppParser = 0;
	if (!cppParser) {
		cppParser = CppParser();
	}
	return findObjCOrObjCppTags(passCount, cppParser);
}

extern parserDefinition* ObjCParser (void)
{
	static const char *const extensions [] = { "m", NULL };
	parserDefinition* def = parserNew ("ObjC");
	def->kinds      = ObjCKinds;
	def->kindCount  = KIND_COUNT (ObjCKinds);
	def->extensions = extensions;
	def->parser2     = findObjCTags;
	return def;
}

extern parserDefinition* ObjCppParser (void)
{
	static const char *const extensions [] = { "mm", NULL };
	parserDefinition* def = parserNew ("ObjC++");
	def->kinds      = ObjCKinds;
	def->kindCount  = KIND_COUNT (ObjCKinds);
	def->extensions = extensions;
	def->parser2     = findObjCppTags;
	return def;
}

extern boolean isObjC()
{
  return getNamedLanguage("ObjC") == File.source.language;
}

extern boolean isObjCKeyword(const char *word)
{
  const char const *keywords[] = { "end",
                                   "extern",
                                   "implementation",
                                   "interface",
                                   "protocol",
                                   "static",
                                   NULL, };
  const char **p = NULL;
  for (p = keywords; *p != NULL; ++p) {
    if (strcmp(*p, word) == 0) {
      return TRUE;
    }
  }
  return FALSE;
}

/**
 * Split str with delimiter.
 * Return an array of splitted strings, which is NULL-terminated.
 * You have to call split_str_free to deallocate a returned value.
 */
extern char **str_split(const char *str, const char *delimiter)
{
  int i;
  char *buf = NULL;
  char **ret = NULL;
  char *p = NULL;

  /* allocate buffer so that we will NOT destory the original string. */
  buf = eMalloc(strlen(str) + 1);
  strcpy(buf, str);

  p = strtok(buf, delimiter);
  i = 0;
  while (p != NULL) {
    ret = eRealloc(ret, (i + 1) * sizeof(*ret));
    ret[i] = eMalloc(strlen(p) + 1);
    strcpy(ret[i], p);
    ++i;
    p = strtok(NULL, delimiter);
  }
  /* terminate ret with NULL */
  ret = eRealloc(ret, (i + 1) * sizeof(*ret));
  ret[i] = NULL;

  eFree(buf);
  buf = NULL;

  return ret;
}

/**
 * Deallocate each element of sarray and sarray itself.
 */
extern void str_split_free(char **sarray)
{
  int i;
  for (i = 0; sarray[i] != NULL; ++i) {
    eFree(sarray[i]);
    sarray[i] = NULL;
  }
  eFree(sarray);
}

/**
 * Concate strings and between.
 * Return a concatenated string.
 * That is to say,
 * return "strings[0]""between""strings[1]""between""strings[2]",
 * if the length of strings is 3.
 * strings should be NULL-terminated.
 * Also you have to free a returned string by yourself.
 */
extern char *str_concat(char **strings, const char *between)
{
  int len = 0, i, n;
  int len_between = strlen(between);
  char *ret = NULL, *p = NULL;

  for (i = 0, n = 0; strings[i] != NULL; ++i, ++n) {
    len += strlen(strings[i]);
    len += len_between;
  }
  len -= len_between;
  /* for null character */
  ++len;

  ret = malloc(sizeof(char) * len);
  memset(ret, '\0', len);
  for (i = 0, p = ret; i < n; ++i) {
    strcpy(p, strings[i]);
    p += strlen(strings[i]);
    if ((i + 1) < n) {
      strcpy(p, between);
      p += len_between;
    }
  }

  return ret;
}

extern const char *processObjCReturnType(const char *returnType)
{
  char **types = str_split(returnType, " ");
  int i, j, numTypes;
  int len = strlen(returnType) + 1;
  char *buf = NULL;
  boolean voidFound = FALSE, constFound = FALSE, someTypeFound = FALSE;
  const char *newReturnType = NULL;

  buf = eMalloc(len);
  memset(buf, '\0', len);

  /* count the elements of types */
  for (i = 0, numTypes = 0; types[i] != NULL; ++i, ++numTypes) {
    /* fprintf(stderr, "DEBUG: types[%d]=%s\n", i, types[i]); */
  }

  for (i = numTypes - 1; i >= 0; --i) {
    if (strcmp(types[i], "void") == 0) {
      voidFound = TRUE;
    }
    else if (strcmp(types[i], "void*") == 0) {
      voidFound = TRUE;
    }
    else if (strcmp(types[i], "const") == 0) {
      constFound = TRUE;
      /* We ignore strings before "const" */
      while (--i >= 0) {
        eFree(types[i]);
        types[i] = NULL;
      }
      break;
    }
    else if (strcmp(types[i], "*") == 0) {
      /* do nothing */
    }
    else {
      if (voidFound || constFound) {
        eFree(types[i]);
        types[i] = NULL;
      }
      else {
        someTypeFound = TRUE;
      }
    }
  }
  /* move elements to the left */
  for (i = 0; i < numTypes - 1; ++i) {
    if (types[i] != NULL) {
      continue;
    }
    else {
      /* move a string into types[i] */
      for (j = i + 1; j < numTypes; ++j) {
        if (types[j] != NULL) {
          types[i] = types[j];
          types[j] = NULL;
          break;
        }
      }
    }
  }
  newReturnType = str_concat(types, " ");
  str_split_free(types);
  eFree(buf);
  return newReturnType;
}

/* vi:set tabstop=4 shiftwidth=4: */
