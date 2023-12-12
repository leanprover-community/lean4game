import * as React from 'react'
import { Input, Typography } from '@mui/material'
import Markdown from '../markdown'
import Switch from '@mui/material/Switch';
import FormControlLabel from '@mui/material/FormControlLabel';

import { IMobileContext } from "../infoview/context"

interface PreferencesPopupProps extends IMobileContext{
    handleClose: () => void
} 

export function PreferencesPopup({ mobile, setMobile, lockMobile, setLockMobile, handleClose }: PreferencesPopupProps) {
    return <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={handleClose} />
        <div className="modal">
            <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
            <Typography variant="body1" component="div" className="settings">
                <div className='preferences-category'>
                    <div className='category-title'>
                        <h3>Mobile layout</h3>
                    </div>
                    <div className='preferences-item'>
                        <FormControlLabel
                            control={
                            <Switch
                                checked={mobile}
                                onChange={() => setMobile(!mobile)}
                                name="checked"
                                color="primary"
                            />
                            }
                            label="Enable"
                            labelPlacement="start"
                        />
                    </div>
                    <div className='preferences-item'>
                        <FormControlLabel
                            control={
                            <Switch
                                checked={!lockMobile}
                                onChange={() => setLockMobile(!lockMobile)}
                                name="checked"
                                color="primary"
                            />
                            }
                            label="Auto"
                            labelPlacement="start"
                        />
                    </div>
                </div>
            </Typography>
        </div>
    </div>
}
