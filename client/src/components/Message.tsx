import * as React from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { Button, Dialog, DialogContent, DialogContentText, DialogActions } from '@mui/material';
import Markdown from './Markdown';

function Message({ isOpen, content, close }) {

  return (
    <Dialog open={isOpen} onClose={close}>
      <DialogContent>
        <DialogContentText id="alert-dialog-description">
          <Markdown>{content}</Markdown>
        </DialogContentText>
      </DialogContent>
      <DialogActions>
        <Button onClick={close} autoFocus={true} disableFocusRipple>
          Ok
        </Button>
      </DialogActions>
    </Dialog>
  )
}

export default Message
